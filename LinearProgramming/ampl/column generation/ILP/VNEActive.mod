set Np ordered; #set of physical nodes
set Ep_u within {i in Np, j in Np: i<j}; #set of physical links
set Nl ordered; #set of logical nodes 
set El_u within Nl cross Nl; #set of logical links
#set El within N cross N; #Used for mapping 

# Is the following lines used to make the link bidirectional?
set Ep within {Np,Np} := Ep_u union setof{(i,j) in Ep_u} (j,i);
#set El within {N,N} := El union setof{(s,t) in El} (t,s); #Used for VNM
set El within {Nl,Nl} := El_u union setof{(s,t) in El_u} (t,s); #Used for VNE
#set El within Nl cross Nl;

set V;
set GEO{Nl} within Np; 
set Nlog{V} within Nl;

# the following two lines are not used now
#param timeIN2 default 0;
#param timeOUT2 default 0;
set L := 1..30;

param M := 70;

var m_s{Np,Nl} binary; #node assignment/mapping
var q_s{Ep,El} binary; #link assignment/mapping
#var w_s{Ep,El,L} binary;

var x_s{El,L} binary ;


minimize Ninterfaces:
	
	# TOTEpL WEpVELENGTHS CONSUMPTION
	sum{(i,j) in Ep, (s,t) in El} q_s[i,j,s,t];
	

# node mapping

s.t. atMostOnePhysicNode {i in Np, vn in V}:
	sum{j in Nlog[vn]} m_s[i,j] <= 1;

s.t. LogicNodeMapping {j in Nl}:
	sum{i in GEO[j]} m_s[i,j] = 1;



# Flow constraints

s.t. flow {(s,t) in El, i in Np}:
	sum{(i,j) in Ep} q_s[i,j,s,t] - sum{(j,i) in Ep} q_s[j,i,s,t] = m_s[i,s]-m_s[i,t];
	

s.t. bidirectionality {(s,t) in El, (i,j) in Ep}:
#s.t. bidirectionality {(s,t) in El, (i,j) in Ep: i in N}:
	q_s[i,j,s,t]-q_s[j,i,t,s]=0;

s.t. biderectionality2 {(s,t) in El, (i,j) in Ep}:
	q_s[i,j,s,t]+q_s[j,i,s,t]<=1;
	