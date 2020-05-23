# test the mapping and the failure model, test wheter the 
# link failure can be detected
set Np ordered; #set of physical nodes
# Ep_u: unidirectional
set Ep_u within {i in Np, j in Np: i<j}; #set of physical links
set Nl ordered; #set of logical nodes 
# El_u: unidirectional
set El_u within Nl cross Nl; #set of logical links
#set El within N cross N; #Used for mapping 

# Is the following lines used to make the link bidirectional?
set Ep within {Np,Np} := Ep_u union setof{(i,j) in Ep_u} (j,i);
#set B within {N,N} := El union setof{(s,t) in El} (t,s); #Used for VNM
set El within {Nl,Nl} := El_u union setof{(s,t) in El_u} (t,s); #Used for VNE

set Dp within Np;
set Df within Np;

set Nf within Np; # set of failed physical nodes
set Ef_u within Ep; # set of failed physical links
set Ef within {Np,Np} := Ef_u union setof{(i,j) in Ef_u} (j,i);

set V;
set GEO{Nl} within Np; 
set Nlog{V} within Nl;
set Dl within Nl;
set Dlog{V} within Nl;
#set Elog{V} within Nl cross Nl;
#set Elog{V} := Elog{V} union setof{(i,j) in Elog{V}} (t,s);
# Elog[v] is the virtual link of virtual network v
set Elog{V} within Nl cross Nl;


# the following two lines are not used now
#param timeIN2 default 0;
#param timeOUT2 default 0;
set L := 1..30;

# the set of stages
#set K := 1..4;
set K;
param Kmax;

# M is greater than number of birectional virtual link in any virtual networks
param M := 25;
param alpha{V};

var m{Np,Nl,K} binary; #node assignment/mapping, assign logical node N1 an physical node N
var q{Ep,El,K} binary; #link assignment/mapping
var m_t{Np,Nl,K} binary; #node assignment/mapping, assign logical node N1 an physical node N
var q_t{Ep,El,K} binary; #link assignment/mapping

param m_s{Np,Nl} binary default 1; #node assignment/mapping, assign logical node N1 an physical node N
param q_s{Ep,El} binary default 1; #link assignment/mapping
param w_s{Ep,El,L} binary default 1;
param x_s{El,L} binary default 1;

var w{Ep,El,L,K} binary;
var y{El,K} binary;
# whether node n is repaired in stage k
var z{Np,K} binary;
# whether link i,j is repaired in stage k
var p{Ep,K} binary;
# whether dc i is repaired in stage k
var b{Dp, K} binary;
# whether dc i is available in stage k
var bCum{Dp, K} binary;
var A{Dl, K} binary;

var beta{Ep, K} binary;
# check whether the logical link works
var beta_log{El, K} binary;


#var z{El,El} binary;

var x{El,L,K} binary ;


#var p >=0 integer;
# assignment of fiber(wavelength)

var f{El,Dl,Nl,K} binary;
var Q{Dl,Nl,K} binary;
var Qbar{Nl,K} binary;

#var z1{Np,El,K} binary;
#var z2{Np,El,K} binary;

# the amount of resources needed for link to be repaired
param r{Np, Np};
# the amount of resources needed for node to be repaired
param h{Np};
# the amount of resources need for data center to be repaired
param g{Dp};
# the amount of resources provided for links in stage k
param R{K};
# the amount of resources provided for nodes in stage k
param H{K};
# the amount of resources provided for data centers in stage k
param G{K};

var S{V, K} binary;

var goal;


# accumulated accumulated weighted virtual networks
maximize accumulatedWeightedConnections:
	goal;

s.t. finalGoal: goal = sum{v in V, k in K} alpha[v] * S[v,k]
;

#s.t. finalGoal: goal = sum{v in V, k in K} alpha[v,k] * S[v,k]
#;

# initialization of working physical nodes/links/dcs
subject to init_link_working1 {(i,j) in Ep diff Ef}:
    p[i,j,0] = 1
;

subject to init_link_working2 {(i,j) in Ep diff Ef, k in 1..Kmax}:
    p[i,j,k] = 0
;

subject to init_link_not_working {(i,j) in Ef}:
    p[i,j,0] = 0
;

subject to init_node_working1 {i in Np diff Nf}:
    z[i,0] = 1
;

subject to init_node_working2 {i in Np diff Nf, k in 1..Kmax}:
    z[i,k] = 0
;

subject to init_node_not_working {i in Nf}:
    z[i,0] = 0
;

subject to init_dc_working1 {i in Dp diff Df}:
    b[i,0] = 1
;

subject to init_dc_not_working {i in Df}:
    b[i,0] = 0
;

subject to init_dc_working2 {i in Dp diff Df, k in 1..Kmax}:
    b[i,k] = 0
;

subject to check_working_link1 {(i,j) in Ep, k in K}:
    beta[i,j,k] <= sum{l in 0..k} p[i,j,l]
;

subject to check_working_link2 {(i,j) in Ep, k in K}:
    beta[i,j,k] <= sum{l in 0..k} z[i,l]
;

subject to check_working_link3 {(i,j) in Ep, k in K}:
    beta[i,j,k] <= sum{l in 0..k} z[j,l]
;

subject to check_working_link4 {(i,j) in Ep, k in K}:
    beta[i,j,k] >= sum{l in 0..k} (p[i,j,l]+z[i,l]+z[j,l]) - 2
;

# 1-beta_log = 0 if right hand side is 0
# 1-beta_log = 1 if right hand side > 0
subject to check_working_logical1 {(s,t) in El, k in K}:
    1 - beta_log[s,t,k] <= sum{(i,j) in Ep} (q[i,j,s,t,k]-q[i,j,s,t,k] * beta[i,j,k])
;

subject to check_working_logical2 {(s,t) in El, k in K}:
    M - beta_log[s,t,k]*M >= sum{(i,j) in Ep} (q[i,j,s,t,k] - q[i,j,s,t,k] * beta[i,j,k])
;

# node mapping

# a physical node maps to at most one virtual node
# in one virtual network
s.t. atMostOnePhysicNode {i in Np, v in V, k in K}:
	sum{j in Nlog[v]} m[i,j,k] <= 1;

# Every virtual node must maps to a physical node
#s.t. LogicNodeMapping {j in Nl, k in K}:
#	sum{i in GEO[j]} m[i,j, k] = 1;
# when one link in a virtual network is not mapped, we
# assume that it cannot be mapped
# don't need to add y[s,t,k]
s.t. LogicNodeMapping1 {v in V, s in Nlog[v], k in K}:
	sum{i in GEO[s]} m[i,s,k] = 1;

# Flow constraints
s.t. flow1 {(s,t) in El, i in Np, k in K}:
	#sum{(i,j) in A} q[i,j,s,t,k] - sum{(j,i) in A} q[j,i,s,t,k] = z1[i,s,t,k] - z2[i,s,t,k];
	sum{(i,j) in Ep} q[i,j,s,t,k] - sum{(j,i) in Ep} q[j,i,s,t,k] = m[i,s,k] - m[i,t,k];

s.t. nocycle1 {i in Np, (s,t) in El, k in K}:
	sum{(i,j) in Ep} q[i,j,s,t,k] <= 1;
s.t. nocycle2 {j in Np, (s,t) in El, k in K}:
	sum{(i,j) in Ep} q[i,j,s,t,k] <= 1;

s.t. bidirectionality1 {(s,t) in El, (i,j) in Ep, k in K}:
	q[i,j,s,t,k]-q[j,i,t,s,k]=0;

s.t. biderectionality2 {(s,t) in El, (i,j) in Ep, k in K}:
	q[i,j,s,t,k]+q[j,i,s,t,k]<=1;

s.t. flowDC {v in V, n in Nlog[v], d in Dlog[v], s in Nlog[v], k in K: d<>n}:
	sum{(s,t) in Elog[v]} f[s,t,d,n,k] - sum{(t,s) in Elog[v]} f[t,s,d,n,k] =
			if s = d then Q[d,n,k]
			else if s = n then -Q[d,n,k]
			else 0 
;

s.t. flowDCFailLink {v in V, n in Nlog[v], d in Dlog[v], (s,t) in Elog[v], k in K: d<>n}:
	f[s,t,d,n,k] <= beta_log[s,t,k]
;

# todo: what if n = d?

s.t. flowDCNode1 {v in V, n in Nlog[v], d in Dlog[v], k in K}:
	Qbar[n,k] >= Q[d,n,k]
;
s.t. flowDCNode2 {v in V, n in Nlog[v], k in K}:
	Qbar[n,k] <= sum{d in Dlog[v]} Q[d,n,k]
;

# Constraints to check whether a virtual network 
# ensures content connectivity
s.t. flowDCVn1 {v in V, n in Nlog[v], k in K}:
	S[v,k] <= Qbar[n,k]
;
s.t. flowDCVn2 {v in V, k in K}:
	S[v,k] >= 1 + sum{n in Nlog[v]} (Qbar[n,k] - 1)
;
s.t. flowDCVn3 {v in V, n in Nlog[v], d in Dlog[v], k in K}:
	Q[d,n,k] <= S[v,k]
;

# add availability of data center
s.t. dcCum {d in Dp, k in K}:
	bCum[d,k] = sum{l in 0..k} b[d,l]
;
s.t. dcLogAvailability {d in Dl, k in K}:
	A[d,k] <= sum{i in Dp} (m[i,d,k] * bCum[i,k])
;

# the data center can provide content only if it is available
s.t. dcAvailableAffectFlow {v in V, n in Nlog[v], d in Dlog[v], k in K}:
	Q[d,n,k] <= A[d,k]
;


#s.t. allUpDown {v in V, (s,t) in Elog[v], k in K}:
#	S[v,k] = y[s,t,k]
#;

# resource constraint
s.t. resourceLink1 {k in K}:
	sum{l in 0..k, (i,j) in Ef_u} p[i,j,l] * r[i,j] <= sum{l in 0..k} R[l]
;
s.t. resourceLink2 {(i,j) in Ef}:
	sum{k in K} p[i,j,k] <=1
;
s.t. resourceLink3 {k in K, (i,j) in Ep}:
	p[i,j,k] = p[j,i,k]
;
s.t. resourceNode1 {k in K}:
	sum{l in 0..k, i in Nf} z[i,l] * h[i] <= sum{l in 0..k} H[l]
;
s.t. resourceNode2 {i in Nf}:
	sum{k in K} z[i,k] <=1
;
s.t. resourceDc1 {k in K}:
	sum{l in 0..k, i in Df} b[i,l] * g[i] <= sum{l in 0..k} G[l]
;
s.t. resourceDc2 {i in Df}:
	sum{k in K} b[i,k] <=1
;

# true mapping of node
s.t. appliedMapingNode1 {v in V, i in Np, s in Nlog[v], k in K}:
	m_t[i,s,k] <= S[v,k]
;
s.t. appliedMapingNode2 {v in V, i in Np, s in Nlog[v], k in K}:
	m_t[i,s,k] <= m[i,s,k]
;
s.t. appliedMapingNode3 {v in V, i in Np, s in Nlog[v], k in K}:
	m_t[i,s,k] >= S[v,k] + m[i,s,k] - 1
;
s.t. appliedMappingLink1 {v in V, (s,t) in Elog[v], (i,j) in Ep, k in K}:
	q_t[i,j,s,t,k] <= S[v,k]
;
s.t. appliedMappingLink2 {v in V, (s,t) in Elog[v], (i,j) in Ep, k in K}:
	q_t[i,j,s,t,k] <= q[i,j,s,t,k]
;
s.t. appliedMappingLink3 {v in V, (s,t) in Elog[v], (i,j) in Ep, k in K}:
	q_t[i,j,s,t,k] >= S[v,k] + q[i,j,s,t,k] - 1
;

# no reconfiguration of node mapping
s.t. noReconfigureNode {v in V, i in Np, s in Nlog[v], k in 1..Kmax}:
	m_t[i,s,k] >= m_t[i,s,k-1]
;

s.t. noReconfigureLink {v in V, (s,t) in Elog[v], (i,j) in Ep, k in 1..Kmax}:
	q_t[i,j,s,t,k] >= q_t[i,j,s,t,k-1]
;


# wavelength assignment
#s.t. continuity1 {(i,j) in Ep, (s,t) in El, l in L, k in K}:
#	w[i,j,s,t,l,k] <= x[s,t,l,k];
#s.t. continuity2 {(i,j) in Ep, (s,t) in El, l in L, k in K}:
#	w[i,j,s,t,l,k] <= q_t[i,j,s,t,k];
#s.t. continuity3 {(i,j) in Ep, (s,t) in El, l in L, k in K}:
#	w[i,j,s,t,l,k] >= x[s,t,l,k] + q_t[i,j,s,t,k] -1;

#s.t. continuity4 {v in V, (s,t) in Elog[v], k in K}:
#	sum{l in L} x[s,t,l,k]= S[v,k];

# wavelength contiguity
#s.t. continuity5 {(i,j) in A, (s1,t1) in B, (s2,t2) in B diff{(s1,t1)}, l in L, k in K}:#:r<>t or u<>s}:
#	w[i,j,s1,t1,l,k]+w[i,j,s2,t2,l,k]<=1;
#s.t. continuity5 {(i,j) in Ep, l in L, k in K}:
#	sum{(s,t) in El} w[i,j,s,t,l,k] <=1;


# todo: I think there is no need to keep this one
#s.t. continuity6 {(i,j) in Ep, (s,t) in El, l in L, k in K}:
#	w[i,j,s,t,l,k] - w[j,i,t,s,l,k] = 0;
