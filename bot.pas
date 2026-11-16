{ A robot on the Clunkyard core's Free Pascal binding. The core owns
  tracking, geometry and protocol handling; this program chooses tactics.
}
(* Clunkyard robot API 2.0.0: one core under every language, the same *)
(* answers everywhere. Facts (a call shows its arguments): *)
(* match: mode ruleset control robots is_3d tick_rate max_ticks *)
(*   robot_id(slot) *)
(* clock: tick seconds remaining_ticks *)
(* arena: size gravity terrain_kind ground_height(x y) *)
(* me: health position velocity heading pitch roll angular_velocity *)
(*   attitude grounded altitude applied hull_mounts to_mount(heading pitch) *)
(*   from_mount(heading pitch) mount_toward(point) *)
(* battery: charge capacity regen sustainable_drive compute *)
(*   drive_cost(fraction) *)
(* drive: hover_lift *)
(* gun: aim_now cooldown_ticks spread max_power damage_scale *)
(*   can_fire(power reserve) shot_speed(power) shot_cost(power) *)
(*   reload_ticks(power) shot_damage(power) power_for_speed(speed) *)
(*   power_for_flight_time(range seconds) lead(contact power) *)
(*   lead_point(position velocity power) *)
(* scanner: last proximity_range reach(arc) arc_for_reach(range) is_on *)
(* sensors: contacts nearest cues contact(slot) position_of(contact) *)
(* tracker: cue nearest_bearing_rate velocity(slot) position(slot) *)
(*   history(slot) last_seen(slot) *)
(* nav: zone zone.margin(point) zone.contains(point margin) *)
(*   zone.distance_from(point) storm storm.margin(point) *)
(*   storm.contains(point margin) storm.distance_from(point) hill *)
(*   hill.margin(point) hill.contains(point margin) *)
(*   hill.distance_from(point) pickups nearest_pickup(kind) *)
(*   field_distance(a b) *)
(* score: me best armour *)
(* angles: normalize(degrees) angle_diff(target current) *)
(*   bearing_to(from to) elevation_to(from to) direction(heading pitch) *)
(*   distance(a b) to_chassis(heading pitch attitude) *)
(*   from_chassis(heading pitch attitude) clamp(value low high) *)
(* raw: number(path) text(path) has(path) flag(path) count(path) line() *)
(* Controls: drive.set(throttle turn pitch_turn) *)
(*   drive.forces(thrust strafe lift yaw_torque pitch_torque roll_torque brake) *)
(*   gun.aim(heading pitch) gun.fire(power) scanner.set(heading arc pitch) *)
(*   scanner.power(on) tracker.configure(smoothing forget_ticks cue_ticks) *)
(*   status.set(text value) debug.log(line) raw.extra(json) *)
(* Every control argument is optional; a second call keeps what the first *)
(* set. Absent facts are your language's none. Names are snake_case here; *)
(* your language cases them its own way. Angles are degrees from the +x *)
(* axis; pitch is positive up. *)
(* Manual: https://clunkyard.com/manual#sdk *)
program Bot;
{$mode objfpc}{$H+}
uses Clunkyard, Math;
type TQuery=function(Robot:TCyRobot;out Value:Double):LongInt;cdecl;
const
  { Bearing is earned: a scan contact's bearing is off by up to its bearing_error
    (degrees, a fixed share of the arc), so a wide beam finds a robot and a narrow one
    aims at it. Contacts within 120 units are exact. }
  SEARCH_ARC=40;  { degrees: sweeps the circle in half a second }
  HOLD_WIDTH=60;  { units across at the target: it stays in the beam from tick to tick }
  MIN_ARC=6;      { degrees: the narrowest the beam holds }
  WINDOW=12;      { ticks of sightings the aim averages }
  SIGHTINGS=8;    { narrow sightings in the window before a shot }
  LOOK_EVERY=40;  { ticks between looks around the target, for a nearer robot }
  REACQUIRE=10;   { ticks to look again where a lost target was }
var Robot:TCyRobot;Status,Event:LongInt;
    DodgeTicks:LongInt=0;Dodges:LongInt=0;Slot:LongInt=0;
function Get(Handle:TCyRobot;Read:TQuery):Double;
var Code:LongInt;
begin Result:=0;Code:=Read(Handle,Result);end;
function Steer(Towards,Current:Double):Double;
var Delta:Double;Code:LongInt;
begin Code:=cy_angles_angle_diff(Towards,Current,Delta);Code:=cy_angles_clamp(Delta/45,-1,1,Result);end;
procedure Drive(Handle:TCyRobot;Throttle,Turning,Pitching:Double);
var Code:LongInt;
begin Code:=cy_drive_throttle(Handle,Throttle);Code:=cy_drive_turn(Handle,Turning);Code:=cy_drive_pitch_turn(Handle,Pitching);end;
procedure Scan(Handle:TCyRobot;Heading,Arc,Pitch:Double);
var Code:LongInt;
begin Code:=cy_scanner_heading(Handle,Heading);Code:=cy_scanner_arc(Handle,Arc);Code:=cy_scanner_pitch(Handle,Pitch);end;
function Coord(const V:TCyVec3;Axis:LongInt):Double;
begin case Axis of 0:Result:=V.X;1:Result:=V.Y;else Result:=V.Z;end;end;
{ A straight line through the narrowest of the last WINDOW ticks' sightings: where
  the robot is now and how fast it moves. Each sighting is off by its bearing_error;
  the line averages that out. }
function Fit(Handle:TCyRobot;Target,Tick:LongInt;out Where,Speed:TCyVec3;out Count:LongInt):Boolean;
var History:array[0..31] of TCySighting;Seen:array[0..31] of LongInt;Total:LongWord;
    I,Axis,Rate,Code:LongInt;Best,T0,Spread,Mean,Slope,Value:Double;Line:array[0..2] of Double;Rates:array[0..2] of Double;
begin
  Result:=False;Count:=0;Where.X:=0;Where.Y:=0;Where.Z:=0;Speed:=Where;
  if cy_tracker_history(Handle,Target,History[0],32,Total)<>CY_OK then Exit;
  Best:=1e30;
  for I:=0 to Total-1 do if History[I].Tick>Tick-WINDOW then if History[I].Bearing_error<Best then Best:=History[I].Bearing_error;
  for I:=0 to Total-1 do if (History[I].Tick>Tick-WINDOW) and (History[I].Bearing_error<=1.5*Best) then begin Seen[Count]:=I;Inc(Count);end;
  if Count<2 then Exit;
  Code:=cy_match_tick_rate(Handle,Rate);T0:=0;
  for I:=0 to Count-1 do T0:=T0+History[Seen[I]].Tick;
  T0:=T0/Count;Spread:=0;
  for I:=0 to Count-1 do Spread:=Spread+Sqr(History[Seen[I]].Tick-T0);
  for Axis:=0 to 2 do begin
    Mean:=0;for I:=0 to Count-1 do Mean:=Mean+Coord(History[Seen[I]].Position,Axis);Mean:=Mean/Count;
    Slope:=0;for I:=0 to Count-1 do Slope:=Slope+(History[Seen[I]].Tick-T0)*(Coord(History[Seen[I]].Position,Axis)-Mean);
    Slope:=Slope/Spread;Line[Axis]:=Mean+Slope*(Tick-T0);Rates[Axis]:=Slope*Rate;
  end;
  Where.X:=Line[0];Where.Y:=Line[1];Where.Z:=Line[2];Speed.X:=Rates[0];Speed.Y:=Rates[1];Speed.Z:=Rates[2];
  Result:=True;
end;
procedure Turn(Handle:TCyRobot);
var Position,Gravity:TCyVec3;Target:TCyContact;Cue:TCyCue;Last:TCyScan;Aim:TCySolution;Now:TCyDirection;
    Storm:TCyStorm;Zone:TCyZone;Code,Tick,Is3d,CanFire,Seen,Count2:LongInt;Ready:Boolean;Where,Speed:TCyVec3;Hold:Double;FreeFlight:Boolean;
    Heading,Pitch,Throttle,Power,Delta,Bearing,Distance,Elevation,Error,Across,Up,Arc,Sweep,Margin,Away,Control,Climb,Turning,Pitching,Work:Double;
    Cues:array[0..31] of TCyContact;Count,I:LongWord;Fired,Left:Boolean;ControlMode:LongInt;
begin
  Code:=cy_me_position(Handle,Position);Code:=cy_arena_gravity(Handle,Gravity);Code:=cy_scanner_last(Handle,Last);
  Heading:=Get(Handle,@cy_me_heading);Pitch:=Get(Handle,@cy_me_pitch);
  Code:=cy_clock_tick(Handle,Tick);Code:=cy_match_is_3d(Handle,Is3d);FreeFlight:=(Is3d<>0) and (Gravity.Z=0);
  Code:=cy_drive_brake(Handle,0.2);
  if cy_sensors_nearest(Handle,Target)=CY_OK then begin
    Slot:=Target.Slot;
    Throttle:=0.2;if Target.Range>350 then Throttle:=0.7 else if Target.Range<200 then Throttle:=-0.4;
    Drive(Handle,Throttle,Steer(Target.Bearing,Heading),Steer(Target.Elevation,Pitch));
    { Halve the beam each tick until it is HOLD_WIDTH across at the target: narrow enough for a precise bearing, wide enough to keep it in. }
    Hold:=Max(MIN_ARC,2*ArcTan2(HOLD_WIDTH/2,Target.Range)*180/Pi);
    { In a crowd a narrow beam sees one robot: every LOOK_EVERY ticks widen it for a tick. }
    if Tick mod LOOK_EVERY=0 then Arc:=SEARCH_ARC else Arc:=Max(Hold,Min(SEARCH_ARC,Last.Arc/2));
    Scan(Handle,Target.Bearing,Arc,Target.Elevation);
    Code:=cy_gun_power_for_flight_time(Handle,Target.Range,1,Power);
    { An exact contact: cy_gun_lead is the intercept if the target holds course.
      A noisy one: lead the fitted line, and fire only once it rests on enough sightings. }
    Ready:=True;
    if Target.Bearing_error>0 then begin
      if Fit(Handle,Slot,Tick,Where,Speed,Count2) then Code:=cy_gun_lead_point(Handle,Where,Speed,Power,Aim)
      else Code:=CY_E_INTERNAL; { no fit: aim at the bearing }
      Ready:=(Code=CY_OK) and (Count2>=SIGHTINGS);
    end else Code:=cy_gun_lead(Handle,Target,Power,Aim);
    if Code<>CY_OK then begin Aim.Heading:=Target.Bearing;Aim.Pitch:=Target.Elevation;end;
    Code:=cy_gun_aim_heading(Handle,Aim.Heading);Code:=cy_gun_aim_pitch(Handle,Aim.Pitch);
    Code:=cy_gun_aim_now(Handle,Now);Code:=cy_angles_angle_diff(Aim.Heading,Now.Heading,Delta);Code:=cy_gun_can_fire(Handle,Power,10,CanFire);
    if Ready and (Abs(Delta)<3) and (Abs(Aim.Pitch-Now.Pitch)<3) and (CanFire<>0) then begin Code:=cy_gun_fire(Handle);Code:=cy_gun_power(Handle,Power);end;
    if Ready then Code:=cy_status_text(Handle,'TRACK',5) else Code:=cy_status_text(Handle,'NARROW',6);
    Code:=cy_status_value(Handle,Target.Range);
  end else if (Slot<>0) and (cy_tracker_last_seen(Handle,Slot,Seen)=CY_OK) and (Tick-Seen<=REACQUIRE) then begin
    { Lost it: look again where it was last seen, widening the beam, before searching. }
    Code:=cy_tracker_position(Handle,Slot,Where);Code:=cy_angles_bearing_to(Position,Where,Bearing);
    Elevation:=0;if FreeFlight then Code:=cy_angles_elevation_to(Position,Where,Elevation);
    Drive(Handle,0.5,Steer(Bearing,Heading),Steer(Elevation,Pitch));
    Scan(Handle,Bearing,Min(SEARCH_ARC,Last.Arc*2),Elevation);Code:=cy_status_text(Handle,'REACQUIRE',9);
  end else if cy_tracker_cue(Handle,Cue)=CY_OK then begin
    Code:=cy_angles_bearing_to(Position,Cue.Position,Bearing);Code:=cy_angles_distance(Position,Cue.Position,Distance);
    Elevation:=0;if FreeFlight then Code:=cy_angles_elevation_to(Position,Cue.Position,Elevation);
    Error:=Min(Cue.Bearing_error,30);Across:=(Tick mod 5-2)/2*Error;Up:=0;if FreeFlight then Up:=((Tick div 5) mod 3-1)*Error/2;
    Drive(Handle,0.7,Steer(Bearing,Heading),Steer(Elevation,Pitch));Code:=cy_scanner_arc_for_reach(Handle,Distance+100,Arc);
    Scan(Handle,Bearing+Across,Arc,Elevation+Up);Code:=cy_status_text(Handle,'CUE',3);Code:=cy_status_value(Handle,Distance);
  end else begin
    Code:=cy_angles_normalize(Last.Heading+36,Sweep);Up:=0;if FreeFlight then Up:=((Tick div 10) mod 3-1)*35;
    Drive(Handle,0.5,0.33,Steer(0,Pitch));Scan(Handle,Sweep,40,Up);Code:=cy_status_text(Handle,'SEARCH',6);
  end;
  { A simple dodge: vary it, or predict the shooter. }
  Fired:=False;
  if cy_sensors_cues(Handle,Cues[0],Length(Cues),Count)=CY_OK then
    for I:=1 to Count do Fired:=Fired or (Cues[I-1].Source=CY_SOURCE_MUZZLE);
  if (DodgeTicks=0) and Fired then begin Inc(Dodges);DodgeTicks:=10;end;
  if DodgeTicks>0 then begin
    { Odd dodges go left, even ones right; turn +1 and strafe -1 go left. }
    Left:=Dodges mod 2=1;if Left then Work:=1 else Work:=-1;Dec(DodgeTicks);
    Code:=cy_match_control(Handle,ControlMode);
    if ControlMode=CY_CONTROL_FORCES then begin Code:=cy_drive_throttle(Handle,0.5);Code:=cy_drive_strafe(Handle,-Work);end
    else begin Code:=cy_drive_throttle(Handle,1);Code:=cy_drive_turn(Handle,Work);end;
    if Left then Code:=cy_status_text(Handle,'dodge:left',10) else Code:=cy_status_text(Handle,'dodge:right',11);
    Code:=cy_status_value(Handle,Dodges);
  end;
  if Get(Handle,@cy_battery_charge)<Get(Handle,@cy_battery_capacity)/4 then Code:=cy_drive_throttle(Handle,Get(Handle,@cy_drive_get_throttle)*0.5);
  if cy_nav_storm(Handle,Storm)=CY_OK then if cy_nav_storm_margin(Handle,Position,Margin)=CY_OK then if Margin>-60 then begin
    Code:=cy_angles_bearing_to(Storm.Center,Position,Away);Code:=cy_angles_angle_diff(Away,Heading,Delta);
    Code:=cy_angles_clamp(Delta/30,-1,1,Control);Code:=cy_drive_throttle(Handle,0.8);Code:=cy_drive_turn(Handle,Control);
  end;
  if cy_nav_zone(Handle,Zone)=CY_OK then if cy_nav_zone_margin(Handle,Position,Margin)=CY_OK then if Margin<60 then begin
    Code:=cy_angles_bearing_to(Position,Zone.Center,Bearing);Climb:=0;if Zone.Shape=CY_SHAPE_SPHERE then Code:=cy_angles_elevation_to(Position,Zone.Center,Climb);
    Code:=cy_angles_angle_diff(Bearing,Heading,Delta);Code:=cy_angles_clamp(Delta/30,-1,1,Turning);
    Code:=cy_angles_clamp((Climb-Pitch)/30,-1,1,Pitching);Drive(Handle,0.8,Turning,Pitching);
  end;
end;
begin
  Status:=cy_open(2,0,'clunkyard-pascal',16,'2.0.0',5,Robot);if Status<0 then Halt(1);
  repeat
    Status:=cy_session_next(Robot,Event);
    if Status=CY_E_INTERNAL then begin Status:=cy_session_send(Robot);if Status<0 then Break;Continue;end;
    if (Status<>CY_OK) or (Event=CY_EVENT_END) then Break;
    if Event=CY_EVENT_STATE then Turn(Robot);
    Status:=cy_session_send(Robot);if Status<0 then Break;
  until False;
  cy_close(Robot);
end.
