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
(*   attitude grounded altitude applied *)
(* battery: charge capacity regen sustainable_drive compute *)
(*   drive_cost(fraction) *)
(* drive: hover_lift *)
(* gun: aim_now cooldown_ticks spread max_power damage_scale *)
(*   can_fire(power reserve) shot_speed(power) shot_cost(power) *)
(*   reload_ticks(power) shot_damage(power) power_for_speed(speed) *)
(*   power_for_flight_time(range seconds) lead(contact power) *)
(*   lead_point(position velocity power) *)
(* scanner: last proximity_range reach(arc) arc_for_reach(range) *)
(* sensors: contacts nearest cues contact(slot) position_of(contact) *)
(* tracker: cue nearest_bearing_rate velocity(slot) position(slot) *)
(*   last_seen(slot) *)
(* nav: zone zone.margin(point) zone.contains(point margin) *)
(*   zone.distance_from(point) storm storm.margin(point) *)
(*   storm.contains(point margin) storm.distance_from(point) hill *)
(*   hill.margin(point) hill.contains(point margin) *)
(*   hill.distance_from(point) pickups nearest_pickup(kind) *)
(*   field_distance(a b) *)
(* score: me best armour *)
(* angles: normalize(degrees) angle_diff(target current) *)
(*   bearing_to(from to) elevation_to(from to) direction(heading pitch) *)
(*   distance(a b) clamp(value low high) *)
(* raw: number(path) text(path) has(path) flag(path) count(path) line() *)
(* Controls: drive.set(throttle turn pitch_turn) *)
(*   drive.forces(thrust strafe lift yaw_torque pitch_torque roll_torque brake) *)
(*   gun.aim(heading pitch) gun.fire(power) scanner.set(heading arc pitch) *)
(*   tracker.configure(smoothing forget_ticks cue_ticks) *)
(*   status.set(text value) raw.extra(json) *)
(* Every control argument is optional; a second call keeps what the first *)
(* set. Absent facts are your language's none. Names are snake_case here; *)
(* your language cases them its own way. Angles are degrees from the +x *)
(* axis; pitch is positive up. *)
(* Manual: https://clunkyard.com/manual#sdk *)
program Bot;
{$mode objfpc}{$H+}
uses Clunkyard, Math;
type TQuery=function(Robot:TCyRobot;out Value:Double):LongInt;cdecl;
var Robot:TCyRobot;Status,Event:LongInt;
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
procedure Turn(Handle:TCyRobot);
var Position,Gravity:TCyVec3;Target:TCyContact;Cue:TCyCue;Last:TCyScan;Aim:TCySolution;Now:TCyDirection;
    Storm:TCyStorm;Zone:TCyZone;Code,Tick,Is3d,CanFire:LongInt;FreeFlight:Boolean;
    Heading,Pitch,Throttle,Power,Delta,Bearing,Distance,Elevation,Error,Across,Up,Arc,Sweep,Margin,Away,Control,Climb,Turning,Pitching,Work:Double;
begin
  Code:=cy_me_position(Handle,Position);Code:=cy_arena_gravity(Handle,Gravity);Code:=cy_scanner_last(Handle,Last);
  Heading:=Get(Handle,@cy_me_heading);Pitch:=Get(Handle,@cy_me_pitch);
  Code:=cy_clock_tick(Handle,Tick);Code:=cy_match_is_3d(Handle,Is3d);FreeFlight:=(Is3d<>0) and (Gravity.Z=0);
  Code:=cy_drive_brake(Handle,0.2);
  if cy_sensors_nearest(Handle,Target)=CY_OK then begin
    Throttle:=0.2;if Target.Range>350 then Throttle:=0.7 else if Target.Range<200 then Throttle:=-0.4;
    Drive(Handle,Throttle,Steer(Target.Bearing,Heading),Steer(Target.Elevation,Pitch));Scan(Handle,Target.Bearing,20,Target.Elevation);
    Code:=cy_gun_power_for_flight_time(Handle,Target.Range,1,Power);
    if cy_gun_lead(Handle,Target,Power,Aim)<>CY_OK then begin Aim.Heading:=Target.Bearing;Aim.Pitch:=Target.Elevation;end;
    Code:=cy_gun_aim_heading(Handle,Aim.Heading);Code:=cy_gun_aim_pitch(Handle,Aim.Pitch);
    Code:=cy_gun_aim_now(Handle,Now);Code:=cy_angles_angle_diff(Aim.Heading,Now.Heading,Delta);Code:=cy_gun_can_fire(Handle,Power,10,CanFire);
    if (Abs(Delta)<3) and (Abs(Aim.Pitch-Now.Pitch)<3) and (CanFire<>0) then begin Code:=cy_gun_fire(Handle);Code:=cy_gun_power(Handle,Power);end;
    Code:=cy_status_text(Handle,'TRACK',5);Code:=cy_status_value(Handle,Target.Range);
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
