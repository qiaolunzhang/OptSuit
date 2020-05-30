param loop_time integer;
param kth_path;
set AE_b := AE union setof{(s,i) in AE} (i,s);
param source symbolic in Nl;
param dest symbolic in Nl;
#set AE_path within {Nl, Np} union {Np, Nl} := setof{i in GEO[source]} (source,i) union
#    setof{i in GEO[dest]} (i,dest);
#set AE_path within {Nl, Np} union {Np, Nl} := setof{i in GEO[source]} (source,i) union{i in GEO[dest]} (i,dest);

param phi1{El_u} default 0;
#param phi2{Ep union AE_b};
param phi2{Ep} default 0;
param phi3{El_u, AE_b} default 0;
#param phi4{El_u,}

#param b{i in V} default if i=source then (- sum{j in V: j<>source} b[j]);
var reducedCostValue;

var f {(i,j) in Ep union AE_b, (s,t) in El_u} binary;
var f_val {(s,t) in El_u} binary;

minimize onePair:
    reducedCostValue
;

#maximize onePair:
#	sum{(s,t) in El_u} f_val[s,t]
#;

s.t. reducedCost:
    reducedCostValue = sum{(i,j) in Ep,(s,t) in El_u} (f[i,j,s,t] - phi2[i,j]*f[i,j,s,t]) 
    				-  sum{(s1,i) in AE_b,(s,t) in El_u} (f[s1,i,s,t] * phi3[s,t,s1,i])
    				- sum{(s,t) in El_u} f_val[s,t] * phi1[s,t]
    #reducedCostValue = sum{(i,j) in Ep} (f[i,j] - phi2[i,j]*f[i,j]) -  sum{(s,i) in AE_path} (f[s,i] * phi3[source,dest,s,i]) - phi1[source,dest]
    #reducedCostValue = sum{(i,j) in Ep} (f[i,j] + phi2[i,j]*f[i,j]) +  sum{(s,i) in AE_path} (f[s,i] * phi3[source,dest,s,i]) - phi1[source,dest]
    #reducedCostValue = sum{(i,j) in Ep union AE_path} (f[i,j] + phi2[i,j]*f[i,j]) +  sum{(s,i) in AE_path} (f[s,i] * phi3[source,dest,s,i]) - phi1[source,dest]
;

s.t. balance1 {i in Np, (s,t) in El_u}:
	sum{(i,j) in Ep union AE_b} f[i,j,s,t] - sum{(j,i) in Ep union AE_b} f[j,i,s,t] = 0;

s.t. balance2 {(s,t) in El_u}:
	sum{(s,j) in Ep union AE_b} f[s,j,s,t] - sum{(j,s) in Ep union AE_b} f[j,s,s,t] = f_val[s,t];

s.t. balance3 {(s,t) in El_u}:
	sum{(t,i) in Ep union AE_b} f[t,i,s,t] - sum{(i,t) in Ep union AE_b} f[i,t,s,t] = -f_val[s,t];
	
s.t. balance4 :
	sum{(s,t) in El_u, (s1,i) in AE} f[s1,i,s,t] <= 1
;

s.t. balance5 {(s,t) in El_u, (i,j) in Ep}:
	f[i,j,s,t] + f[j,i,s,t] <=1
;

s.t. notMappedSame {(s,t) in El_u}:
	sum{(i,j) in Ep} f[i,j,s,t] >= f_val[s,t];
	#sum{(i,j) in Ep} f[i,j] + sum{(i,j) in AE_path} f[i,j] >= 4;
	
s.t. oneOut {i in Np,(s,t) in El_u}:
	sum{(i,j) in Ep union AE_b} f[i,j,s,t] <= 1
;

s.t. oneIn {j in Np,(s,t) in El_u}:
	sum{(i,j) in Ep union AE_b} f[i,j,s,t] <= 1
;

s.t. oneFlow:
	sum{(s,t) in El_u} f_val[s,t] <= 1
;
#problem pricing: f, f_val, reducedCostValue, onePair, reducedCost, balance1, balance2, balance3, balance4, notMappedSame, oneOut, oneIn, oneFlow;
#problem pricing: f, f_val, reducedCostValue, onePair, reducedCost, balance1, balance2, balance3, balance4, balance5, notMappedSame, oneOut, oneIn, oneFlow;
problem pricing: f, f_val, reducedCostValue, onePair, reducedCost, balance1, balance2, balance3, balance4, balance5, notMappedSame, oneOut, oneIn, oneFlow;
