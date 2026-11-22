{ Narrow the scan around a contact and lead shots from recent sightings. }
(* Clunkyard guide: https://clunkyard.com/sdk/pascal *)

program Bot;
{$mode objfpc}{$H+}

uses Clunkyard, Math;

type
  TQuery = function (Robot: TCyRobot; out Value: Double): LongInt; cdecl;

const
  SEARCH_ARC = 40;  { degrees: sweeps the circle in half a second }
  HOLD_WIDTH = 60;  { units across at the target: it stays in the beam from tick to tick }
  MIN_ARC = 6;      { degrees: the narrowest the beam holds }
  WINDOW = 12;      { ticks of sightings the aim averages }
  SIGHTINGS = 8;    { narrow sightings in the window before a shot }
  LOOK_EVERY = 40;  { ticks between looks around the target, for a nearer robot }
  REACQUIRE = 10;   { ticks to look again where a lost target was }
var
  DodgeTicks, Dodges: LongInt;
  Slot: LongInt = 0;

function Get(Handle:TCyRobot;Read:TQuery): Double;
var Code: LongInt;
begin
  Result := 0;
  Code := Read(Handle,Result);
end;

function Steer(Towards,Current:Double): Double;
var Delta: Double;
  Code: LongInt;
begin
  Code := cy_angles_angle_diff(Towards,Current,Delta);
  Code := cy_angles_clamp(Delta/45,-1,1,Result);
end;

procedure Drive(Handle:TCyRobot;Throttle,Turning,Pitching:Double);
var Code: LongInt;
begin
  Code := cy_drive_throttle(Handle,Throttle);
  Code := cy_drive_turn(Handle,Turning);
  Code := cy_drive_pitch_turn(Handle,Pitching);
end;

procedure Scan(Handle:TCyRobot;Heading,Arc,Pitch:Double);
var Code: LongInt;
begin
  Code := cy_scanner_heading(Handle,Heading);
  Code := cy_scanner_arc(Handle,Arc);
  Code := cy_scanner_pitch(Handle,Pitch);
end;

function Coord(const V:TCyVec3;Axis:LongInt): Double;
begin
  case Axis of
    0: Result := V.X;
    1: Result := V.Y;
    else Result := V.Z;
  end;
end;

{ A straight line through the narrowest of the last WINDOW ticks' sightings: where
  the robot is now and how fast it moves. Each sighting is off by its bearing_error;
  the line averages that out. }
function Fit(Handle:TCyRobot;Target,Tick:LongInt;out Where,Speed:TCyVec3;out Count:LongInt): Boolean;
var History: array[0..31] of TCySighting;
  Seen: array[0..31] of LongInt;
  Total: LongWord;
  I,Axis,Rate,Code: LongInt;
  Best,T0,Spread,Mean,Slope,Value: Double;
  Line: array[0..2] of Double;
  Rates: array[0..2] of Double;
begin
  Result := False;
  Count := 0;
  Where.X := 0;
  Where.Y := 0;
  Where.Z := 0;
  Speed := Where;
  if cy_tracker_history(Handle,Target,History[0],32,Total)<>CY_OK Then Exit;
  Best := 1e30;
  for I:=0 to Total-1 do
    if History[I].Tick>Tick-WINDOW Then if History[I].Bearing_error<Best Then Best := History[I].Bearing_error;
  for I:=0 to Total-1 do
    if (History[I].Tick>Tick-WINDOW) and (History[I].Bearing_error<=1.5*Best) Then
      begin
        Seen[Count] := I;
        Inc(Count);
      end;
  if Count<2 Then Exit;
  Code := cy_match_tick_rate(Handle,Rate);
  T0 := 0;
  for I:=0 to Count-1 do
    T0 := T0+History[Seen[I]].Tick;
  T0 := T0/Count;
  Spread := 0;
  for I:=0 to Count-1 do
    Spread := Spread+Sqr(History[Seen[I]].Tick-T0);
  for Axis:=0 to 2 do
    begin
      Mean := 0;
      for I:=0 to Count-1 do
        Mean := Mean+Coord(History[Seen[I]].Position,Axis);
      Mean := Mean/Count;
      Slope := 0;
      for I:=0 to Count-1 do
        Slope := Slope+(History[Seen[I]].Tick-T0)*(Coord(History[Seen[I]].Position,Axis)-Mean);
      Slope := Slope/Spread;
      Line[Axis] := Mean+Slope*(Tick-T0);
      Rates[Axis] := Slope*Rate;
    end;
  Where.X := Line[0];
  Where.Y := Line[1];
  Where.Z := Line[2];
  Speed.X := Rates[0];
  Speed.Y := Rates[1];
  Speed.Z := Rates[2];
  Result := True;
end;

procedure Turn(Handle:TCyRobot);
var Position,Gravity: TCyVec3;
  Target: TCyContact;
  Cue: TCyCue;
  Last: TCyScan;
  Aim: TCySolution;
  Now: TCyDirection;
  Storm: TCyStorm;
  Zone: TCyZone;
  Code,Tick,Is3d,CanFire,Seen,Count2: LongInt;
  Ready: Boolean;
  Where,Speed: TCyVec3;
  Hold: Double;
  FreeFlight: Boolean;
  Heading,Pitch,Throttle,Power,Delta,Bearing,Distance,Elevation,Error,Across,Up,Arc,Sweep,Margin,Away,Control,Climb,Turning,Pitching,Work: Double;
  Cues: array[0..31] of TCyContact;
  Count,I: LongWord;
  Fired,Left: Boolean;
  ControlMode: LongInt;
begin
  Code := cy_me_position(Handle,Position);
  Code := cy_arena_gravity(Handle,Gravity);
  Code := cy_scanner_last(Handle,Last);
  Heading := Get(Handle,@cy_me_heading);
  Pitch := Get(Handle,@cy_me_pitch);
  Code := cy_clock_tick(Handle,Tick);
  Code := cy_match_is_3d(Handle,Is3d);
  FreeFlight := (Is3d<>0) and (Gravity.Z=0);
  Code := cy_drive_brake(Handle,0.2);
  if cy_sensors_nearest(Handle,Target)=CY_OK Then
    begin
      Slot := Target.Slot;
      Throttle := 0.2;
      if Target.Range>350 Then Throttle := 0.7
      else if Target.Range<200 Then Throttle := -0.4;
      Drive(Handle,Throttle,Steer(Target.Bearing,Heading),Steer(Target.Elevation,Pitch));
    { Halve the beam each tick until it is HOLD_WIDTH across at the target: narrow enough for a precise bearing, wide enough to keep it in. }
      Hold := Max(MIN_ARC,2*ArcTan2(HOLD_WIDTH/2,Target.Range)*180/Pi);
    { In a crowd a narrow beam sees one robot: every LOOK_EVERY ticks widen it for a tick. }
      if Tick mod LOOK_EVERY=0 Then Arc := SEARCH_ARC
      else Arc := Max(Hold,Min(SEARCH_ARC,Last.Arc/2));
      Scan(Handle,Target.Bearing,Arc,Target.Elevation);
      Code := cy_gun_power_for_flight_time(Handle,Target.Range,1,Power);
    { An exact contact: cy_gun_lead is the intercept if the target holds course.
      A noisy one: lead the fitted line, and fire only once it rests on enough sightings. }
      Ready := True;
      if Target.Bearing_error>0 Then
        begin
          if Fit(Handle,Slot,Tick,Where,Speed,Count2) Then Code := cy_gun_lead_point(Handle,Where,Speed,Power,Aim)
          else Code := CY_E_INTERNAL; { no fit: aim at the bearing }
          Ready := (Code=CY_OK) and (Count2>=SIGHTINGS);
        end
      else Code := cy_gun_lead(Handle,Target,Power,Aim);
      if Code<>CY_OK Then
        begin
          Aim.Heading := Target.Bearing;
          Aim.Pitch := Target.Elevation;
        end;
      Code := cy_gun_aim_heading(Handle,Aim.Heading);
      Code := cy_gun_aim_pitch(Handle,Aim.Pitch);
      Code := cy_gun_aim_now(Handle,Now);
      Code := cy_angles_angle_diff(Aim.Heading,Now.Heading,Delta);
      Code := cy_gun_can_fire(Handle,Power,10,CanFire);
      if Ready and (Abs(Delta)<3) and (Abs(Aim.Pitch-Now.Pitch)<3) and (CanFire<>0) Then
        begin
          Code := cy_gun_fire(Handle);
          Code := cy_gun_power(Handle,Power);
        end;
      if Ready Then Code := cy_status_text(Handle,'TRACK',5)
      else Code := cy_status_text(Handle,'NARROW',6);
      Code := cy_status_value(Handle,Target.Range);
    end
  else if (Slot<>0) and (cy_tracker_last_seen(Handle,Slot,Seen)=CY_OK) and (Tick-Seen<=REACQUIRE) Then
         begin
    { Lost it: look again where it was last seen, widening the beam, before searching. }
           Code := cy_tracker_position(Handle,Slot,Where);
           Code := cy_angles_bearing_to(Position,Where,Bearing);
           Elevation := 0;
           if FreeFlight Then Code := cy_angles_elevation_to(Position,Where,Elevation);
           Drive(Handle,0.5,Steer(Bearing,Heading),Steer(Elevation,Pitch));
           Scan(Handle,Bearing,Min(SEARCH_ARC,Last.Arc*2),Elevation);
           Code := cy_status_text(Handle,'REACQUIRE',9);
         end
  else if cy_tracker_cue(Handle,Cue)=CY_OK Then
         begin
           Code := cy_angles_bearing_to(Position,Cue.Position,Bearing);
           Code := cy_angles_distance(Position,Cue.Position,Distance);
           Elevation := 0;
           if FreeFlight Then Code := cy_angles_elevation_to(Position,Cue.Position,Elevation);
           Error := Min(Cue.Bearing_error,30);
           Across := (Tick mod 5-2)/2*Error;
           Up := 0;
           if FreeFlight Then Up := ((Tick div 5) mod 3-1)*Error/2;
           Drive(Handle,0.7,Steer(Bearing,Heading),Steer(Elevation,Pitch));
           Code := cy_scanner_arc_for_reach(Handle,Distance+100,Arc);
           Scan(Handle,Bearing+Across,Arc,Elevation+Up);
           Code := cy_status_text(Handle,'CUE',3);
           Code := cy_status_value(Handle,Distance);
         end
  else
    begin
      Code := cy_angles_normalize(Last.Heading+36,Sweep);
      Up := 0;
      if FreeFlight Then Up := ((Tick div 10) mod 3-1)*35;
      Drive(Handle,0.5,0.33,Steer(0,Pitch));
      Scan(Handle,Sweep,40,Up);
      Code := cy_status_text(Handle,'SEARCH',6);
    end;
  { A simple dodge: vary it, or predict the shooter. }
  Fired := False;
  if cy_sensors_cues(Handle,Cues[0],Length(Cues),Count)=CY_OK Then
    for I:=1 to Count do
      Fired := Fired or (Cues[I-1].Source=CY_SOURCE_MUZZLE);
  if (DodgeTicks=0) and Fired Then
    begin
      Inc(Dodges);
      DodgeTicks := 10;
    end;
  if DodgeTicks>0 Then
    begin
    { Odd dodges go left, even ones right; turn +1 and strafe -1 go left. }
      Left := Dodges mod 2=1;
      if Left Then Work := 1
      else Work := -1;
      Dec(DodgeTicks);
      Code := cy_match_control(Handle,ControlMode);
      if ControlMode=CY_CONTROL_FORCES Then
        begin
          Code := cy_drive_throttle(Handle,0.5);
          Code := cy_drive_strafe(Handle,-Work);
        end
      else
        begin
          Code := cy_drive_throttle(Handle,1);
          Code := cy_drive_turn(Handle,Work);
        end;
      if Left Then Code := cy_status_text(Handle,'dodge:left',10)
      else Code := cy_status_text(Handle,'dodge:right',11);
      Code := cy_status_value(Handle,Dodges);
    end;
  if Get(Handle,@cy_battery_charge)<Get(Handle,@cy_battery_capacity)/4 Then Code := cy_drive_throttle(Handle,Get(Handle,@cy_drive_get_throttle)*0.5);
  if cy_nav_storm(Handle,Storm)=CY_OK Then if cy_nav_storm_margin(Handle,Position,Margin)=CY_OK Then if Margin>-60 Then
                                                                                                       begin
                                                                                                         Code := cy_angles_bearing_to(Storm.Center,Position,Away);
                                                                                                         Code := cy_angles_angle_diff(Away,Heading,Delta);
                                                                                                         Code := cy_angles_clamp(Delta/30,-1,1,Control);
                                                                                                         Code := cy_drive_throttle(Handle,0.8);
                                                                                                         Code := cy_drive_turn(Handle,Control);
                                                                                                       end;
  if cy_nav_zone(Handle,Zone)=CY_OK Then if cy_nav_zone_margin(Handle,Position,Margin)=CY_OK Then if Margin<60 Then
                                                                                                    begin
                                                                                                      Code := cy_angles_bearing_to(Position,Zone.Center,Bearing);
                                                                                                      Climb := 0;
                                                                                                      if Zone.Shape=CY_SHAPE_SPHERE Then Code := cy_angles_elevation_to(Position,
                                                                                                                                                 Zone.Center,Climb);
                                                                                                      Code := cy_angles_angle_diff(Bearing,Heading,Delta);
                                                                                                      Code := cy_angles_clamp(Delta/30,-1,1,Turning);
                                                                                                      Code := cy_angles_clamp((Climb-Pitch)/30,-1,1,Pitching);
                                                                                                      Drive(Handle,0.8,Turning,Pitching);
                                                                                                    end;
end;
begin
  cy_run(@Turn);
end.
