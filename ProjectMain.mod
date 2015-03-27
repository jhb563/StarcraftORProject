param T;
set Times := 1..T;
set Buildings;
set Units;

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

param totalSuppyCap >= 0;