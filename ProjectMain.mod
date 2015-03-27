param T;
set Times := 1..T;
set Buildings;
set Units ordered;

param BuildTimes{Buildings} >= 0;
param TrainTimes{Units} >= 0;
param startMinerals >= 0;
param startGas >= 0;

param unitSupply{Units} >= 0;
param BuildingCost{Buildings} >= 0;
param BuildingCostGas{Buildings} >= 0;
param UnitCost{Units} >= 0;
param UnitCostGas{Units} >= 0;
param init{Units} >= 0;
param mineralRatePerWorker >= 0;
param gasRatePerWorker >= 0;
param totalSupplyCap >= 0;
param buildingSupply{Buildings} >= 0;
param requiredForBuilding{Buildings,Buildings} >= 0;
param canBuildUnit{Buildings,Units} >= 0;


var minerals{Times} >= 0;
var gas{Times} >= 0;
var totalUnits{Times,Units} >= 0;
var inTraining{Times,Units} >= 0;
var startTraining{Times,Units} >= 0;
var buildingNum{Times,Buildings} >= 0;
var buildingStart{Times,Buildings} >= 0;
var mineralMinersNum{Times} >= 0;
var gasMinersNum{Times} >= 0;
var currentSupplyCap{Times} >= 0;


subject to initialMineralsConstraint:
minerals[0] = startMinerals;

subject to initialGasConstraint:
gas[0] = startGas;

# At each time step, our current mineral level is what we previously had,
# minus the amount we spend on units and buildings, plus what our workers
# gathered in that time
subject to mineralDelta{t in 2..T}:
minerals[t] = minerals[t - 1] + mineralMinersNum[t - 1] * mineralRatePerWorker - (sum{b in Buildings} (buildingStart[t,b]*BuildingCost[b])) - (sum{u in Units} (startTraining[t,u]*unitCost[u]));

# Same for gas
subject to gasDelta{t in 2..T}:
gas[t] = gas[t-1] + gasMinersNum[t-1] * gasRatePerWorker - (sum{b in Buildings} (buildingStart[t,b]*buildingCost[b])) - (sum{u in Units} (startTraining[t,u]*unitCost[i]));

# Assume that the probe is the "first" unit in the units set
subject to totalWorkersConstraint{t in Times}:
mineralMinersNum[t] + gasMinersNum[t] <= totalUnits[t,0];

# Can't get over 200 supply, both with total units and those in training
subject to maximumSupplyConstraint{t in Times}:
(sum{u in Units} (totalUnits[t,u] * unitSupply[u]) + inTraining[t,u] * unitSupply[u]) <= totalSupplyCap;


# Can't exceed our current supply allotment
subject to currentSupplyConstraint{t in Times}:
(sum{u in Units} (totalUnits[t,u] * unitSupply[u] + inTraining[t,u] * unitSupply[u])) <= currentSupplyCap[t];

# Our current supply is the amount supplied by our buildings
subject to buildingSupplyCap{t in Times}:
currentSupplyCap[t] <= (sum{b in Buildings} (buildingNum[b] * buildingSupply[b]));

# We start with certain units
subject to initalUnitsConstraint{u in Units}:
totalUnits[0,u] = init[u];


