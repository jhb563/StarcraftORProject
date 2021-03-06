# The amount of seconds we are simulating in the game
param T;



############
# SETS
############

# Each game second up until the time we care about
set Times := 0..T;
# The different buildings the race can build
set Buildings;
# The different units the race can build. Ordered so that we
# can refer to the worker as index 0.
set Units ordered;

##############
# PARAMETERS
##############

# Large constant
param M >= 0;

# Build times, costs, supply provided (buildings) or supply cost (units)
param BuildTime{Buildings} >= 0;
param BuildingCost{Buildings} >= 0;
param BuildingCostGas{Buildings} >= 0;
param buildingSupply{Buildings} >= 0;
param TrainTime{Units} >= 0;
param UnitCost{Units} >= 0;
param UnitCostGas{Units} >= 0;
param unitSupply{Units} >= 0;

# Hierarchy Requirements (what buildings are required for what, which
# buildings build which units)
param requiredForBuilding{Buildings,Buildings} >= 0;
param canBuildUnit{Buildings,Units} >= 0;
param buildingRequiredForUnit{Buildings,Units} >= 0;

# Initial Conditions
param startMinerals >= 0;
param startGas >= 0;
param init{Units} >= 0;
param initialBuildings{Buildings} >= 0;

# Game invariants
param mineralRatePerWorker >= 0;
param gasRatePerWorker >= 0;
param totalSupplyCap >= 0;


####################
# DECISION VARIABLES
####################

# Resources at each second of the game
var minerals{Times} >= 0;
var gas{Times} >= 0;

# At some time, we have a certain amount of units done, some in training, and
# some just started (this is sort've a meta-parameter)
var totalUnits{Times,Units} >= 0 integer;
var inTraining{Times,Units} >= 0 integer;
var startTraining{Times,Units} >= 0 integer;

# At each time, we have some buildings, and some start being built at certain
# times.
var buildingNum{Times,Buildings} >= 0 integer;
var buildingStart{Times,Buildings} >= 0 integer;

# The amount of workers we have devoted to minerals and gas at a given
# moment.
var mineralMinersNum{Times} >= 0 integer;
var gasMinersNum{Times} >= 0 integer;

# Our current maximum supply
var currentSupplyCap{Times} >= 0 integer;

####################
# OBJECTIVE FUNCTION
####################

maximize gold:
totalUnits[T,'zealot'] + 2*totalUnits[T,'stalker'];

#############
# CONSTRAINTS
#############

# Initial condition constraints
subject to initialMineralsConstraint:
minerals[0] = startMinerals;

subject to initialGasConstraint:
gas[0] = startGas;

subject to initalUnitsConstraint{u in Units, t in Times:t <= TrainTime[u]}:
totalUnits[t,u] = init[u];

subject to initialBuildingsConstraint{b in Buildings, t in Times:t <= BuildTime[b]}:
buildingNum[t,b] = initialBuildings[b];

# At each time step, our current mineral level is what we previously had,
# minus the amount we spend on units and buildings, plus what our workers
# gathered in that time
subject to mineralDelta{t in 1..T}:
minerals[t] = minerals[t - 1] + mineralMinersNum[t - 1] * mineralRatePerWorker - (sum{b in Buildings} (buildingStart[t,b]*BuildingCost[b])) - (sum{u in Units} (startTraining[t,u]*UnitCost[u]));

# Same for gas
subject to gasDelta{t in 1..T}:
gas[t] = gas[t-1] + gasMinersNum[t-1] * gasRatePerWorker - (sum{b in Buildings} (buildingStart[t,b]*BuildingCostGas[b])) - (sum{u in Units} (startTraining[t,u]*UnitCostGas[u]));

# We can only mine 3 workers per assimilator
subject to assimilatorConstraint{t in 1..T}:
gasMinersNum[t] - 3*buildingNum[t,'assimilator'] <= 0;

# We can only work as many workers as we have
subject to totalWorkersConstraint{t in Times}:
mineralMinersNum[t] + gasMinersNum[t] = totalUnits[t,'probe'];

# Can't get over 200 supply, both with total units and those in training
subject to maximumSupplyConstraint{t in Times}:
(sum{u in Units} ((totalUnits[t,u] * unitSupply[u]) + (inTraining[t,u] * unitSupply[u]))) <= totalSupplyCap;



# Can't exceed our current supply allotment
subject to currentSupplyConstraint{t in Times}:
(sum{u in Units} (totalUnits[t,u] * unitSupply[u] + inTraining[t,u] * unitSupply[u])) <= currentSupplyCap[t];

# Our current supply is the amount supplied by our buildings
subject to buildingSupplyCap{t in Times}:
currentSupplyCap[t] = (sum{b in Buildings} (buildingNum[t,b] * buildingSupply[b]));

# We have as many buildings as we had previously, plus any that were starting at
# the time previously that would finish exactly now
subject to buildingCountConstraint{b in Buildings, t in Times:t > BuildTime[b]}:
buildingNum[t,b] = buildingNum[t-1,b] + buildingStart[t-BuildTime[b]+1,b];

# Units have a similar constraint to buildings
subject to unitCountConstraint{u in Units, t in Times:t > TrainTime[u]}:
totalUnits[t,u] = totalUnits[t-1,u] + startTraining[t-TrainTime[u]+1,u];

# You cannot start making more units than you have structures for.
subject to buildingTrainingConstraint{u in Units, t in Times}:
inTraining[t,u] <= (sum{b in Buildings} (canBuildUnit[b,u]*buildingNum[t,b]));

# For each unit, the number in training is equal to the amount that have started 
# in the period of the unit's build time.
subject to trainingStartedConstraint{u in Units, t in Times:t >= TrainTime[u]}:
inTraining[t,u] = (sum{x in (t-TrainTime[u])..t} startTraining[x,u]);

# Same constraint as above, just early on:
subject to trainingStartedConstraintEarly{u in Units, t in Times:t < TrainTime[u]}:
inTraining[t,u] = (sum{x in 0..t} startTraining[x,u]);



# Building Requirements Constraints
# Each building can only start if its requirement has been made
subject to buildingRequirement{t in Times, b1 in Buildings, b2 in Buildings}:
buildingStart[t,b1] <= M*(1-requiredForBuilding[b1,b2])+M*buildingNum[t,b2];



# Technology Constraints
# Units can only be built if the right buildings are there
subject to unitTechnology{t in Times, u in Units, b in Buildings}:
startTraining[t,u] <= M*(1-buildingRequiredForUnit[b,u]) + M*buildingNum[t,b];
