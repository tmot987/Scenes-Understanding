%% This program represents a scenario where the robot has to pick objects up,
%% and put them down in kid's room.
%% For picking up: 
%%   - the first step is recognizing the sought object;
%%   - an object may not be considered not found if there is some occluded object in the scene;
%%   - the occlusion and stability are considered;
%%   - occluded objects are considered to be identified as soon as all the occlusion is removed.
%% For putting down:
%%   - the candidate locations have to be found (considering stability and occlusion).
%%   - The object can't be placed in a location that cause instability. 

#const numSteps = 9.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 sorts
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% sorts for different objects
#books = [book][1..3].
#blocks = [block][1..2].
#small_blocks = {small_block0}.
#duck = {duck1}.
#unknown = [unknown][0..2]. % this sort is for the partially occluded and not identified objects

#object = #books + #small_blocks + #duck + #unknown + #blocks.

#location = #object+{ground}.

% Objects attributes:
#obj_size = {small, medium, large}. 
#top_surface = {irregular, flat}.

% Agent sort
#robot = {rob1}.

% Spatial relations changed from fluents to sorts for facilitating generalization over relation's properties.
#positions = {front, behind, above, below, left, right}.
#distances = {touch, not_touch, far}.
#composed_rel = {on}.

#spatial_rel = #composed_rel +  #positions + #distances .

#boolean = {true, false}.

#step = 0..numSteps.

%%%%%%%%%%
%% Fluents
%%%%%%%%%%

#inertial_fluent = stable(#object) + partial_occluded(#object,#object) + in_hand(#robot, #object) + relation(#spatial_rel, #location, #location) + absent(#location) + small_base(#object).

#defined_fluent = occluded(#object). % object occluded if any partial occlusion due to one or more objects exists

#fluent = #inertial_fluent + #defined_fluent.

%%%%%%%%%%
%% Actions
%%%%%%%%%%

#action = pickup(#robot, #object) + putdown(#robot, #object, #object).




%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 predicates
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

has_surface(#object, #top_surface).

has_size(#object, #obj_size).

complement(#spatial_rel, #spatial_rel).

identity(#unknown, #location). % this is the "secret" identity of the so far not identified objects.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% other predicates
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
holds(#fluent,#step).
occurs(#action,#step).
scene_stable(#step).

obs(#fluent, #boolean, #step).
hpd(#action, #step).

success().
goal(#step). 
something_happened(#step).

%val(#fluent, #boolean, #step).
is_defined(#fluent).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
rules
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% SPATIAL RELATIONS %%

% some attributes rules.
complement(SR1, SR2) :- complement(SR2, SR1), SR1!=SR2.

% spatial relation attributes:
complement(right, left).
complement(front, behind).
complement(above, below).

% definition of ON relation as ABOVE + TOUCH
holds(relation(on, O1, O2), I) :- holds(relation(above, O1, O2), I), holds(relation(touch, O1, O2), I).
holds(relation(above, O1, O2), I) :- holds(relation(on, O1, O2), I).
holds(relation(touch, O1, O2), I) :- holds(relation(on, O1, O2), I).

% all distance relations are commutative
holds(relation(D, O1, O2), I) :- holds(relation(D, O2, O1), I), #distances(D).

% relations that present commutative properties between each other
holds(relation(S1, O1, O2), I) :- holds(relation(S2, O2, O1), I), complement(S2, S1). %   CREATING INCONSISTANCY WITHOUT THE FOLLOWING AXIOM:
-holds(relation(S1, O1, O2), I) :- -holds(relation(S2, O2, O1), I), complement(S2, S1).

% 2 objects can't hold more than 1 positional spatial relation at the same time:
-holds(relation(SR1, O1, O2), I) :- holds(relation(SR2, O1, O2), I), SR1!=SR2, #positions(SR1), #positions(SR2).

% the spatial relations still hold if the unknown object is identified
holds(relation(S, O, L), I) :- holds(relation(S, U, L), I), identity(U, O), -holds(absent(O), I).


% An object is considered to have a small base if it is placed above a small object
holds(small_base(O1), I) :- holds(relation(above, O1, O2), I), has_size(O2, small).


%% OCCLUSION %%

% An object is considered to be occluded if it is partially occluded by any other object
holds(occluded(O1), I) :- holds(partial_occluded(O1, O2), I).



%% ABSENCE %%%

% An object is considered not to be absent if it holds any spatial relation with another object
-holds(absent(O), I) :- holds(relation(SR, O, L), I).

% An object is considered to become identified (not absent) when it is not occluded
-holds(absent(O), I) :- -holds(occluded(U), I), identity(U, O), #unknown(U).



%% PUT DOWN %%

%% Putting down an object causes it to be ON another object
holds(relation(on, O1, O2), I+1) :- occurs(putdown(R, O1, O2), I), O1!=O2.

%% All objects have to be placed in stable configurations
holds(stable(O1), I). % this axiom must be removed in case of scene classification

%% Every objects (except the ground) only supports one object at a time
-occurs(putdown(R, O1, O), I) :- holds(relation(on, O2, O), I), O1!=O2, #object(O).

%% Putting an object down causes it to no longer be in hand.
-holds(in_hand(R, O), I+1) :- occurs(putdown(R, O, L), I), O!=L.

%% Cannot put down an object unless it is in hand...
-occurs(putdown(R, O, L), I) :- -holds(in_hand(R,O), I).

%% Cannot put down an object in a specific location if the location is not found
-occurs(putdown(R, O, L), I) :- holds(absent(L), I).

% The whole scene is considered unstable if any object is unstable in a scene...
-scene_stable(I) :- -holds(stable(O),I).
% ... otherwise, the scene is stable.
scene_stable(I) :- not -scene_stable(I).


%% PICK UP %%

%% Picking up an object causes object to be in hand.
holds(in_hand(R, O), I+1) :- occurs(pickup(R, O), I).

% Picking up an object results in the removal of the current spatial relations.
-holds(relation(SR, O1, O2), I+1) :- occurs(pickup(R, O1), I), #object(O1), holds(relation(SR, O1, O2), I).

% For picking up an previously not identified object, the relations of its UNKNOWN counterpart have to be removed.
-holds(relation(SR, U1, O2), I+1) :- occurs(pickup(R, O1), I), #object(O1), holds(relation(SR, U1, O2), I), identity(U1, O1).

%% Cannot pick up an object if it already has it (or another one) in hand.
-occurs(pickup(R, O1), I) :- holds(in_hand(R, O2), I).

%% Cannot pick up an object if it is not identified (absent).
-occurs(pickup(R, O), I) :- holds(absent(O), I), #object(O).

%% Picking an object up is not allowed if it is below another object.
-occurs(pickup(R, A), I) :- holds(relation(below, A, B), I).

%% Picking an object up is not allowed if it is behind another object.
-occurs(pickup(R, A), I) :- holds(relation(behind, A, B), I).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Learned Rules
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% An object not presenting the spatial relation ABOVE with any other object is STABLE.
holds(stable(A), I) :- -holds(relation(above, A, B), I), #object(B). 

%% An object placed ABOVE another object with irregular top surface is UNSTABLE.
-holds(stable(A), I) :- holds(relation(above, A, B), I), has_surface(B, irregular).

%% An object is not partially occluded by another if it is not BEHIND it.
-holds(partial_occluded(A, B), I) :- -holds(relation(behind, A ,B), I).

% An object is usually unstable when it is above a small base. 
-holds(stable(A), I) :- holds(small_base(A), I).%, not holds(stable(A), I).
%holds(stable(A), 0) :+ holds(small_base(A), 0).

% An object "A" placed above other object "C" tends to avoid a possible occlusion caused by a third object "B", from which it is placed behind.
-holds(partial_occluded(A, B), I) :- holds(relation(behind, A ,B), I), holds(relation(above, A, C), I), #object(C).%, not holds(partial_occluded(A, B), I).%
%holds(partial_occluded(A, B), I) :+.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 


% More attributes:

% ducks have irregular top surface
has_surface(O, irregular) :- #duck(O).

% small_blocks are small
has_size(O, small) :- #small_blocks(O).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%       
%% Inertial axiom + CWA

%% General inertia axioms...
holds(F,I+1) :- #inertial_fluent(F),
                holds(F,I),
                not -holds(F,I+1).

-holds(F,I+1) :- #inertial_fluent(F),
                 -holds(F,I),
                 not holds(F,I+1).
  
%% CWA for Defined Fluents...
-holds(F,I) :- #defined_fluent(F),         
                 not holds(F,I).
               
%% CWA for Actions...
-occurs(A,I) :- not occurs(A,I).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%       
%% History and initial state rules

%% Take what actually happened into account...
occurs(A,I) :- hpd(A,I).

%% Reality check axioms...
:- obs(F, true, I), -holds(F, I).
:- obs(F, false, I), holds(F, I).

is_defined(F) :- obs(F, Y, 0).
-holds(F, 0) :- #inertial_fluent(F),
		not is_defined(F), not holds(F, 0).

%% Awareness axiom...
%holds(F, 0) | -holds(F, 0) :- #inertial_fluent(F).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%       
%% Planning Module

%% Failure is not an option...
success :- goal(I).
:- not success. 

%% Cannot be idle while goal remains unachieved...
occurs(A, I) | -occurs(A, I) :- not goal(I). 

%% Cannot execute two actions at the same time...
:- occurs(A1,I), occurs(A2,I), A1 != A2.

something_happened(I) :- occurs(A, I).
:- not goal(I), 
   not something_happened(I).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%
%%Initial State:
%%%%%%%%%%%%%%%%

%% INITIAL RELATIONS INVOLVING OBJECTS. This information and the objects recognition would be captured from the camera. Not identified objects are initially labeled as UNKNOWN[i]. 
holds(relation(above, unknown0, ground),0).
holds(relation(above, book1, unknown0),0).
holds(relation(above, small_block0, book1),0).
holds(relation(behind, unknown0, duck1),0).
holds(relation(behind, unknown0, book3),0).

holds(relation(left, block1, duck1),0).
holds(relation(right, block2, duck1),0).

%% All the objects in the database and not initially identified are considered absent.
holds(absent(unknown1),0).
holds(absent(unknown2),0).
holds(absent(book2),0).

%% The partial occlusion can also be captured from scene.
holds(partial_occluded(unknown0, duck1),0).
holds(partial_occluded(unknown0, book3),0).

%% In a real robot the identity function is not needed; as soon as an object is identified, the UNKNOWN[i] label is replaced by the correct name. 
identity(unknown0, book2).

%% The objects are initially considered to be stable. 
holds(stable(O),0).% :- -holds(absent(O),0).


goal(I) :- holds(in_hand(rob1,book2), I).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%       
display
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%       
occurs.
%scene_stable.
%holds(occluded(O),I).
