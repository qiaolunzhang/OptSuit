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

# surrogate relaxation multipliers
param m1{1..M} default 0;
param m2{1..M} default 0;
param m3{1..M} default 0;

param m1_old{1..M} default 1;
param m2_old{1..M} default 1;
param m3_old{1..M} default 1;

# step for updating multipliers
param t default 1;

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


#----------------------------------------------------------
# Surrogate Relaxation
#----------------------------------------------------------

subject to SurrogateCapacity {j in 1..M}:
	sum {i in 1..N} m1[j]*w[i]*x[i,j] - m1[j]*B_c*y[j] + sum {i in 1..N} m2[j]*cpu[i]*x[i,j] - m2[j]*B_CPU * y[j]
	+ sum {i in 1..N} m3[j]*m[i]*x[i,j] - m3[j] *B_m * y[j] <= 0
;
