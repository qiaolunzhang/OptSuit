param source symbolic in Nl;
param dest symbolic in Nl;
set AE_b := AE union setof{(s,i) in AE} (i,s);
set AE_path within {Nl, Np} union {Np, Nl} := setof{i in GEO[source]} (source,i) union
    setof{i in GEO[dest]} (i,dest);
#set AE_path within {Nl, Np} union {Np, Nl} := setof{i in GEO[source]} (source,i) union{i in GEO[dest]} (i,dest);

param phi1{El_u};
#param phi2{Ep union AE_b};
param phi2{Ep};
param phi3{El_u, AE_b};

