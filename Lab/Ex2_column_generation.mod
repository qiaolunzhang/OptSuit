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

#number of clusters
param S default N;
#cluster composition
param a{1..N, 1..S} default 0;

# dual variable
param pi{1..N} >= 0, default 0;

# VM selection 
var l{1..S} >=0;

minimize UsedVM:
	sum{i in 1..S} l[i];
;

s.t. cover{i in 1..N}:
	sum{j in 1..S} a[i,j]*l[j] >=1
;

		#####################
		#  PRICING PROBLEM	#
		#####################	

# variables
# composition of the new cluster
var u{1..N}, binary;

minimize reducedCost:
	1 - sum {i in 1..N} u[i] * pi[i]
;

s.t. trafficCapacity:
	sum {i in 1..N} w[i] * u[i] <= B_c
;

s.t. cpuCapacity {j in 1..M}:
	sum {i in 1..N} cpu[i] * u[i] <= B_CPU
;

s.t. memoryCapacity {j in 1..M}:
	sum {i in 1..N} m[i] * u[i] <= B_m
;

#PROBLEM DEFINITION

problem master: l, UsedVM, cover; 

problem pricing: u, reducedCost, trafficCapacity, cpuCapacity, memoryCapacity;