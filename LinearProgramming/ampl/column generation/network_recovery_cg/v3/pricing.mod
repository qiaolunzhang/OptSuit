param loop_time integer;
param kth_path;
set AE_b := AE union setof{(s,i) in AE} (i,s);
set AE_path within {Nl, Np} union {Np, Nl} := setof{i in GEO[source]} (source,i) union
    setof{i in GEO[dest]} (i,dest);
#set AE_path within {Nl, Np} union {Np, Nl} := setof{i in GEO[source]} (source,i) union{i in GEO[dest]} (i,dest);

param phi1{El_u,K} default 0;
#param phi2{Ep union AE_b};
param phi2{Ep,K} default 0;
param phi3{El_u, AE_b,K} default 0;
#param phi4{El_u,}

#param b{i in V} default if i=source then (- sum{j in V: j<>source} b[j]);
var reducedCostValue;

var f {(i,j) in Ep union AE_path} binary;

minimize onePair:
    reducedCostValue
;

s.t. reducedCost:
    reducedCostValue = -1 - sum{(i,j) in Ep} (phi2[i,j,stage]*f[i,j]) 
    		-  sum{(s,i) in AE_path} (f[s,i] * phi3[source,dest,s,i,stage]) 
    		- phi1[source,dest,stage]
    #reducedCostValue = sum{(i,j) in Ep} (f[i,j] - phi2[i,j]*f[i,j]) -  sum{(s,i) in AE_path} (f[s,i] * phi3[source,dest,s,i]) - phi1[source,dest]
    #reducedCostValue = sum{(i,j) in Ep} (f[i,j] + phi2[i,j]*f[i,j]) +  sum{(s,i) in AE_path} (f[s,i] * phi3[source,dest,s,i]) - phi1[source,dest]
    #reducedCostValue = sum{(i,j) in Ep union AE_path} (f[i,j] + phi2[i,j]*f[i,j]) +  sum{(s,i) in AE_path} (f[s,i] * phi3[source,dest,s,i]) - phi1[source,dest]
;

s.t. balance1 {i in Np}:
	sum{(i,j) in Ep union AE_path} f[i,j] - sum{(j,i) in Ep union AE_path} f[j,i] = 0;

s.t. balance2:
	sum{(source,j) in Ep union AE_path} f[source,j] - sum{(j,source) in Ep union AE_path} f[j,source] = 1;

s.t. balance3:
	sum{(dest,i) in Ep union AE_path} f[dest,i] - sum{(i,dest) in Ep union AE_path} f[i,dest] = -1;

s.t. notMappedSame {i in Np: (source,i) in AE and (dest,i) in AE}:
	f[source,i] + f[i,dest] <=1;
	
s.t. oneOut {i in Np}:
	sum{(i,j) in Ep union AE_path} f[i,j] <= 1
;
s.t. oneIn {j in Np}:
	sum{(i,j) in Ep union AE_path} f[i,j] <= 1
;

problem pricing: f, reducedCostValue, onePair, reducedCost, balance1, balance2, balance3, notMappedSame, oneOut, oneIn;