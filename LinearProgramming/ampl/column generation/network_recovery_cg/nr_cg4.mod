# set of physical nodes


set Np ordered;
set Nl ordered; #set of logical nodes 

# Ep_u: unidirectional
set Ep_u within {i in Np, j in Np: i<j}; #set of physical links
# El_u: unidirectional
set El_u within Nl cross Nl; #set of logical links

set Ep within {Np,Np} := Ep_u union setof{(i,j) in Ep_u} (j,i);
set El within {Nl,Nl} := El_u union setof{(s,t) in El_u} (t,s); #Used for VNE

set GEO{Nl} within Np;

set Nf within Np; # set of failed physical ndoes
set Ef_u within Ep_u; # set of failed physical links
set Ef within {Np, Np} := Ef_u union setof{(i,j) in Ef_u} (j,i);

# the virtual networks
set V;
set Nlog{V} within Nl;
set Elog{V} within Nl cross Nl;

# actually for one path, we need to include two link to it, one is to enter the physical network, the other is to
# exit the physical network, however, we only consider the direction from virtual to physical
set AE within {Nl, Np} := setof{s in Nl, i in GEO[s]} (s,i);
#set AE within ({Np, Nl} union {Nl, Np}) := setof{s in Nl, i in GEO[s]} (s,i) union setof{s in Nl, i in GEO[s]} (i,s);

set K;

param Kmax;


#param n_path_total integer;
# the number of path for each virtual link
param n_path {El_u} integer;

param c{(s,t) in El_u, 1..n_path[s,t]};

param L;

#set path_total {1..n_path_total} within Ep union AE;
set path_link {(s,t) in El_u, 1..n_path[s,t]} within (Ep union AE);

# the amount of resources needed for link to be repaired
param r{Np, Np};
# the amount of resources needed for node to be repaired
param h{Np};
# the amount of resources provided for links in stage k
param R{K};
# the amount of resources provided for nodes in stage k
param H{K};

#var q
#var q{(s,t) in El_u, 1..n_path[s,t], k in K} binary;
var q{(s,t) in El_u, 1..n_path[s,t], k in K} <=1, >=0;
# 1 if the virtual node s is mapped to the physical node i
# todo: check whether we need to replace GEO[s] with Np

#var m{s in Nl, i in GEO[s], k in K} binary;
var m{s in Nl, i in GEO[s], k in K} <=1, >=0;

#var beta{Ep, K} binary;
var beta{Ep, K} <=1, >=0;
#var beta_log{El, K} binary;
var beta_log{El, K} <=1, >=0;

# whether node n is repaired in stage k
#var z{Np,K} binary;
var z{Np,K} <=1, >=0;

# whether link i,j is repaired in stage k
#var p{Ep,K} binary;
var p{Ep,K} <=1, >=0;


param delta{(s,t) in El_u, AE, 1..n_path[s,t]} binary, default 0;

# add a path, we need to change
# n_path: the number of path for each virtual link
# path_link: all the links in a path
# delta: the node mapping for a path


param source symbolic in Nl;
param dest symbolic in Nl;
param stage symbolic in K;


minimize cost:
#maximize cost:
    sum{(s,t) in El_u, path in 1..n_path[s,t], k in K} -q[s,t,path,k]
    #sum{(s,t) in El_u, k in K} beta_log[s,t,k]
    #sum{(s,t) in El_u, path in 1..n_path[s,t]} c[s,t,path] * q[s,t,path]
;

#minimize cost:
    #sum{(s,t) in El_u, path in 1..n_path[s,t]} c[s,t,path] * q[s,t,path]
#;


# initialization of working physical nodes/links/dcs
subject to init_link_working1 {(i,j) in Ep diff Ef}:
    p[i,j,0] = 1
;

#subject to init_link_working2 {(i,j) in Ep diff Ef, k in 1..Kmax}:
#    p[i,j,k] = 0
#;

subject to init_link_not_working {(i,j) in Ef}:
    p[i,j,0] = 0
;

#s.t. linkKeepState {(i,j) in Ep, k in 1..Kmax}:
#    p[i,j,k] >= p[i,j,k-1]
#;

subject to init_node_working1 {i in Np diff Nf}:
    z[i,0] = 1
;

#subject to init_node_working2 {i in Np diff Nf, k in 1..Kmax}:
#    z[i,k] = 0
#;

subject to init_node_not_working {i in Nf}:
    z[i,0] = 0
;

#s.t. nodeKeepState {i in Np, k in 1...Kmax}:
#    z[i,k] >= z[i,k-1]
#;

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


# a physical node can be mapped to at most one virtual node in a virtual network
s.t. atMostOnePhysicNode {i in Np, v in V, k in K}:
	sum{s in Nlog[v]: (s,i) in AE} m[s,i,k] <= 1
	#sum{s in Nlog[v]} m[s,i] <= 1
;

# a logical node s must be mapped to exactly one physical node
s.t. LogicNodeMapping1 {s in Nl,k in K}:
    # here (s,i) must belong to AE
	sum{i in GEO[s]} m[s,i,k] = 1
;

# a logical node s must be mapped to exactly one a physical node
#s.t. LogicNodeMapping1 {v in V, s in Nlog[v]}:
#	sum{i in GEO[s]} m[s,i] = 1;
# phi1
s.t. flowPath {(s,t) in El_u,k in K}:
    sum{path in 1..n_path[s,t]} q[s,t,path,k] <= 1;
;

# if it's not an optical network and the traffic is unsplitable, we only need to add another
# value: the request in the link multiply q
#s.t. linkCapacity {(i,j) in Ep_u union AE}:
# phi2
s.t. linkCapacity {(i,j) in Ep_u,k in K}:
    # consider two direction for the capacity
    sum{(s,t) in El_u, path in 1..n_path[s,t]: (i,j) in path_link[s,t,path] or (j,i) in path_link[s,t,path]} q[s,t,path,k] 
        <= L * beta[i,j,k]
    #sum{(s,t) in El_u, path in 1..n_path[s,t]: (i,j) in path_link[s,t,path]} q[s,t,path] <= L
;

# phi3
s.t. flowNodeMapping {(s,t) in El_u, (s1,i) in AE, k in K}:
    sum{path in 1..n_path[s,t]} delta[s,t,s1,i,path] * q[s,t,path,k] <= m[s1,i,k]
    #sum{path in n_path[s,t]} delta[s,t,i]
;

#s.t. linkWorkingCapacity {(i,j) in Ep_u,k in K}:
#    sum{(s,t) in El_u, path in 1..n_path[s,t]: (i,j) in path_link[s,t,path] or (j,i) in path_link[s,t,path]} q[s,t,path,k] <= L * beta[i,j,k]
#;


s.t. workingBidirectional1 {(i,j) in Ep_u, k in K}:
    beta[i,j,k] = beta[j,i,k]
;

s.t. workingBidirectional2 {(s,t) in El_u, k in K}:
    beta_log[s,t,k] = beta_log[t,s,k]
;

#s.t. check_working_logical {(s,t) in El_u, (i,j) in Ep, k in K}:
#    sum{path in 1..n_path[s,t]: (i,j) in path_link[s,t,path]} (beta_log[s,t,k] * q[s,t,path,k]) <= beta[i,j,k]
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

problem master: q, m, beta, beta_log, z, p, cost, atMostOnePhysicNode,LogicNodeMapping1,flowPath,linkCapacity,flowNodeMapping,
                workingBidirectional1, workingBidirectional2,
                resourceLink1, resourceLink2, resourceLink3,
                resourceNode1, resourceNode2,
                init_link_working1, 
                init_link_not_working,
                init_node_working1, 
                init_node_not_working,
                check_working_link1, check_working_link2, check_working_link3, check_working_link4
                ;