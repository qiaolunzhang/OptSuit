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


#param n_path_total integer;
# the number of path for each virtual link
param n_path {El_u} integer;

param c{(s,t) in El_u, 1..n_path[s,t]};

param L;

#set path_total {1..n_path_total} within Ep union AE;
set path_link {(s,t) in El_u, 1..n_path[s,t]} within (Ep union AE);

#var q
var q{(s,t) in El_u, 1..n_path[s,t]} binary;
#var q{(s,t) in El_u, 1..n_path[s,t]} <=1, >=0;
# 1 if the virtual node s is mapped to the physical node i
# todo: check whether we need to replace GEO[s] with Np
var m{s in Nl, i in GEO[s]} binary;
#var m{s in Nl, i in GEO[s]} <=1, >=0;

var beta{Ep} binary;
var beta_log{El} binary;

# whether node n is repaired in stage k
var z{Np} binary;
# whether link i,j is repaired in stage k
var p{Ep} binary;

param delta{(s,t) in El_u, AE, 1..n_path[s,t]} binary, default 0;

# add a path, we need to change
# n_path: the number of path for each virtual link
# path_link: all the links in a path
# delta: the node mapping for a path


minimize cost:
    #sum{(i,j) in Ep} (1-beta[i,j])
    sum{(s,t) in El_u, path in 1..n_path[s,t]} c[s,t,path] * q[s,t,path]
;

# initialization of working physical nodes/links/dcs
subject to init_link_working1 {(i,j) in Ep diff Ef}:
    p[i,j] = 1
;


subject to init_link_not_working {(i,j) in Ef}:
    p[i,j] = 0
;

subject to init_node_working1 {i in Np diff Nf}:
    z[i] = 1
;

subject to init_node_not_working {i in Nf}:
    z[i] = 0
;

#subject to check_working_link1 {(i,j) in Ep}:
#    beta[i,j] <= p[i,j]
#;

#s.t. check_working_link2 {(i,j) in Ep}:
#    beta[i,j] <= z[i]
#;

#s.t. check_working_link3 {(i,j) in Ep}:
#    beta[i,j] <= z[j]
#;

#s.t. check_working_link4 {(i,j) in Ep}:
#    beta[i,j] >= p[i,j]+z[i]+z[j] - 2
#;

# a physical node can be mapped to at most one virtual node in a virtual network
s.t. atMostOnePhysicNode {i in Np, v in V}:
	sum{s in Nlog[v]: (s,i) in AE} m[s,i] <= 1
	#sum{s in Nlog[v]} m[s,i] <= 1
;

# a logical node s must be mapped to exactly one physical node
s.t. LogicNodeMapping1 {s in Nl}:
    # here (s,i) must belong to AE
	sum{i in GEO[s]} m[s,i] = 1
;

# a logical node s must be mapped to exactly one a physical node
#s.t. LogicNodeMapping1 {v in V, s in Nlog[v]}:
#	sum{i in GEO[s]} m[s,i] = 1;

s.t. flowPath {(s,t) in El_u}:
    sum{path in 1..n_path[s,t]} q[s,t,path] = 1;
;

# if it's not an optical network and the traffic is unsplitable, we only need to add another
# value: the request in the link multiply q
#s.t. linkCapacity {(i,j) in Ep_u union AE}:
s.t. linkCapacity {(i,j) in Ep_u}:
    # consider two direction for the capacity
    sum{(s,t) in El_u, path in 1..n_path[s,t]: (i,j) in path_link[s,t,path] or (j,i) in path_link[s,t,path]} q[s,t,path] <= L
    #sum{(s,t) in El_u, path in 1..n_path[s,t]: (i,j) in path_link[s,t,path]} q[s,t,path] <= L
;

s.t. flowNodeMapping {(s,t) in El_u, (s1,i) in AE}:
    sum{path in 1..n_path[s,t]} delta[s,t,s1,i,path] * q[s,t,path] <= m[s1,i]
    #sum{path in n_path[s,t]} delta[s,t,i]
;

#s.t. flowNodeMapping2 {(s,t) in El_u, i in Np: (t,i) in AE}:
    #let AE_path := setof{i in GEO[source]} (source,i) union
    #    setof{i in GEO[dest]} (i,dest);
#    sum{path in 1..n_path[s,t]} delta[s,t,i,path] * q[s,t,path] <= m[t,i]
#;

problem master: q, m, cost, atMostOnePhysicNode,LogicNodeMapping1,flowPath,linkCapacity,flowNodeMapping,
                init_link_working1, init_link_not_working, init_node_working1, init_node_not_working
                #,check_working_link1, check_working_link2, check_working_link3, check_working_link4;