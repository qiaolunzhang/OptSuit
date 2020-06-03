#PARAMETERS

#number of requests
param N; 

#number of virtual machine
param M;

#request traffic
param w{1..N};

#request CPU requirement
param cpu{1..N} default 1;

#request memory requirement
param m{1..N} default 1;

#VM capacity
param B_c;
#VM max CPU
param B_CPU default N;
#VM max memory
param B_m default N;

# x equals to 1 if requests i is assigned to virtual machine j
var x{1..N, 1..M} binary;
# y equals to 1 if virtual machine j is instantiated
var y{1..M} binary;

minimize UsedVM:
	sum {j in 1..M} y[j]
;

s.t. trafficCapacity {j in 1..M}:
	sum {i in 1..N} w[i] * x[i,j] <= B_c * y[j]
;

s.t. cpuCapacity {j in 1..M}:
	sum {i in 1..N} cpu[i] * x[i,j] <= B_CPU * y[j]
;

s.t. memoryCapacity {j in 1..M}:
	sum {i in 1..N} m[i] * x[i,j] <= B_m * y[j]
;

s.t. assignedOneServer {i in 1..N}:
	sum {j in 1..M} x[i,j] = 1
;