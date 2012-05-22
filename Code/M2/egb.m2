listFromMHT = h -> (
     l := new MutableList;
     i := 0;
     while h#? i do (
	  l#i = h#i;
	  i = i+1;
	  );
     return new List from l;
     )

divWitness = (v,w) -> (
     v = (listForm v)#0#0;
     w = (listForm w)#0#0;
     n := length v;
     sigma := new MutableHashTable;
     i := n-1;
     for j in reverse(0..n-1) do (
	  while v#i == 0 and i >= 0 do i = i-1;
	  if j > i then continue;
	  if v#i <= w#j then (
	       sigma#j = i;
	       i = i-1;
	       )
	  );
     if #sigma != #select(v,a -> a != 0) then return (false, {});
     i = n-1;
     for j in reverse(0..n-1) do (
	  if not sigma#? j then (
	       while v#i != 0 and i >= 0 do i = i-1;
	       sigma#j = i;
	       i = i-1;
	       );
	  );
     sigma = listFromMHT(sigma);
     assert(length sigma == n);
     return (true, sigma);
     )

permute = (b,sigma) -> (
     X := gens ring b;
     s := apply(length X, i -> (X#(sigma#i) => X#i));
     return sub(b,s);
     )

spoly = (f,g) -> (
     l = lcm(leadMonomial f,leadMonomial g);
     return (l//(leadTerm f))*f - (l//(leadTerm g))*g;
     )

nextPerm = P -> (
     n := #P;
     i := 1;
     while i < n and P#(i-1) > P#i do i = i+1;
     if i == n then return new MutableList;
     Q := sort new List from take(P,i);
     apply(i, k -> (P#k = Q#k));
     j := 1;
     while j < i and P#j < P#i do j = j+1;
     a := P#i;
     P#i = P#(j-1);
     P#(j-1) = a;
     return P;
     )

allPerms = n -> (
     Perms := new MutableList;
     p := new MutableList from (0..n-1);
     while #p != 0 do (
	  Perms#(#Perms) = new List from p;
	  p = nextPerm(p);
	  );
     return new List from Perms;
     )

reduce = (f,B) -> (
     R := ring f;
     r := 0;
     while f != 0 do (
	  divOccurred := false;
	  for b in B do (
	       (isDiv, sigma) = divWitness(b,f);
	       --print (isDiv, sigma);
	       if isDiv then (
		    sb := permute(b,sigma);
		    f = spoly(f,sb);
		    divOccurred = true;
		    break;
		    );
	       );
	  if not divOccurred then (
	       r = r + leadTerm f;
	       f = f - leadTerm f;
	       );
	  );
     return r;
     )

interreduceGB = G -> ( -- !!!

     )

reduceGB = G -> (
     G = select(G, g -> (
	       keep := true;
	       for f in G do (
		    if f != g and (divWitness(f,g))#0 then keep = false;
		    );
      	       if not keep then <<"r"<<flush;
	       return keep;
	       )
	  );
     return apply(G, g -> (g//leadCoefficient g));
     )
			 

truncatedGB = F -> (
     R := ring F#0;
     n := numgens R;
     Perms := allPerms(n);
     i := 0;
     while i < #F do (
	  for j from 0 to i do (
	       --s := new MutableList from (0..n-1);
	       --while #s != 0 do (
	       for s in Perms do (
		    --t := new MutableList from (0..n-1);
		    --while #t != 0 do (
		    for t in Perms do (
			 f := spoly(permute(F#i,s), permute(F#j,t));
			 r := reduce(f,F);
			 --if f != 0 then print (permute(F#i,s), permute(F#j,t),f,r);
			 if r != 0 then (<<"n"<<flush; F = --interreduceGB 
			      append(F,r));
			 --t = nextPerm(t);
			 );
		    --s = nextPerm(s);
		    );
	       );
	  i = i+1;
	  );
     return reduceGB F;
     )

end

load "SymmetricGB.m2"
R = QQ[x_3,x_2,x_1, MonomialOrder => Lex]
f = x_3^2*x_2^2 + x_2*x_1
B = {x_3*x_1 + x_2*x_1}
reduce(f,B)
f = x_2*x_1
B = {x_2 + x_1, x_2*x_1}
reduce(f,B)

v = x_1*x_3^2
w = x_2^3*x_3^2
sigma = divWitness(v,w)
permute(v,sigma#1)

P = new MutableList from (0..4)
while #P != 0 do (print (new List from P); P = nextPerm(P))
allPerms 4

restart
load "egb.m2"
R = QQ[x_2,x_1, MonomialOrder => Lex]
F = {x_1 + x_2, x_1*x_2}
truncatedGB F
R = QQ[x_3,x_2,x_1, MonomialOrder => Lex]
truncatedGB apply(F, f->sub(f,R))
R = QQ[x_4,x_3,x_2,x_1, MonomialOrder => Lex]
truncatedGB apply(F, f->sub(f,R))

R = QQ[x_3,x_2,x_1, MonomialOrder => Lex]
F = {x_1^3*x_3+x_1^2*x_2^3, x_2^2*x_3^2-x_2^2*x_1+x_1*x_3^2};
R = QQ[x_4,x_3,x_2,x_1, MonomialOrder => Lex];
truncatedGB apply(F, f->sub(f,R))
R = QQ[x_5,x_4,x_3,x_2,x_1, MonomialOrder => Lex];
truncatedGB apply(F, f->sub(f,R))


