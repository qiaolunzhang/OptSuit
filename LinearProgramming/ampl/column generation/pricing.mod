#param b{i in V} default if i=source then (- sum{j in V: j<>source} b[j]);
var reducedCostValue;

var f {(i,j) in Ep union AE_path} binary;

minimize onePair:
    reducedCostValue
;

s.t. reducedCost:
    reducedCostValue = sum{(i,j) in Ep} (f[i,j] + phi2[i,j]*f[i,j]) +  sum{(s,i) in AE_path} (f[s,i] * phi3[source,dest,s,i]) - phi1[source,dest]
    #reducedCostValue = sum{(i,j) in Ep union AE_path} (f[i,j] + phi2[i,j]*f[i,j]) +  sum{(s,i) in AE_path} (f[s,i] * phi3[source,dest,s,i]) - phi1[source,dest]
;

s.t. balance1 {i in Np}:
	sum{(i,j) in Ep union AE_path} f[i,j] - sum{(j,i) in Ep union AE_path} f[j,i] = 0;

s.t. balance2:
	sum{(source,j) in Ep union AE_path} f[source,j] - sum{(j,source) in Ep union AE_path} f[j,source] = 1;

s.t. balance3:
	sum{(dest,i) in Ep union AE_path} f[dest,i] - sum{(i,dest) in Ep union AE_path} f[i,dest] = -1;

s.t. notMappedSame:
	sum{(i,j) in Ep} f[i,j] >= 1;
	#sum{(i,j) in Ep} f[i,j] + sum{(i,j) in AE_path} f[i,j] >= 4;

problem pricing: f, reducedCostValue, onePair, reducedCost, balance1, balance2, balance3, notMappedSame;