listFromMHT = h -> (
     l := new MutableList;
     i := 0;
     while h#? i do (
	  l#i = h#i;
	  i = i+1;
	  );
     return toList l;
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

gDivWitness = (v,w) -> (
     -- << "gDivWitness(" << leadMonomial v << "," << leadMonomial w << ") = ";
     v = (listForm leadTerm v)#0#0;
     w = (listForm leadTerm w)#0#0;
     n := length v;
     sigma := new MutableHashTable;
     i := n-1;
     for j in reverse(0..n-1) do
	  if v#i <= w#j then (
	       sigma#j = i; 
	       i = i-1;
	       );
     for j in reverse(0..n-1) do
	  if not sigma#? j then (
	       if v#i != 0 then (
		    --print "not divisible"; 
		    return (false, {})
		    );
	       sigma#j = i;
	       i = i-1;
	       );
     sigma = listFromMHT(sigma);
     assert(length sigma == n);
     -- print sigma;
     return (true, sigma);
     )

permute = (b,sigma) -> (
     X := gens ring b;
     s := apply(length X, i -> (X#(sigma#i) => X#i));
     sub(b,s)
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

reduce = method(Options=>{Completely=>false})
reduce (RingElement, BasicList) := o -> (f,B) -> (
     B' := select(toList B,b->b!=0);
     R := ring f;
     divisionOccured := true;
     while divisionOccured and f != 0 do (
	  divisionOccured = false;
	  local divisible; local sigma;
	  divisors := select(1, B', b->(
		    (divisible, sigma) = gDivWitness(b,f);
		    divisible
		    ));
	  if #divisors>0 then (
	       sb := permute(first divisors,sigma); -- currenly "divisors" is a list of one element
	       --print(leadMonomial sb, leadMonomial f);
	       --assert(lcm(leadMonomial f, leadMonomial sb)==leadMonomial f);
	       f = f - (leadTerm f//leadTerm sb)*sb;
	       divisionOccured = true;
	       );
	  );
     if not o.Completely or f == 0 then f
     else leadTerm f + reduce(f - leadTerm f, B', Completely=>true) 
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

processSpairs = method(Options=>{Symmetrize=>true})
processSpairs (List,ZZ) := o -> (F,k) -> (
     if o.Symmetrize then F = interreduce'symmetrize F; 
     R := ring F#0;
     n := numgens R;
     x := symbol x;
     R' := (coefficientRing R)[reverse(x_0..x_(n+k-1)), MonomialOrder => Lex];
     RtoR' := map(R',R, drop(gens R',k));
     F = F/RtoR';
     sp := shiftPairs(R',k);
     print apply(sp,t->matrix first t||matrix last t);
     nF := #F;
     F' := {};
     scan(nF, i->
	  scan(i+1, j->(
		    --if i!=j then
		    for st in sp do (
		    	 (s,t) := st;
		    	 f := spoly(s F#i, t F#j);
		    	 r := reduce(f,F);
		    	 --if f != 0 then print (i,j,s,t);
		    	 if r != 0 then (
			      << "(n)"; 
			      -- if i==j then print(F#i,F#j,r,matrix s,matrix t);
			      F' = append(F',r)
			      );
		    	 );
	       	    ))
	  );
     interreduce(F|F', Symmetrize => o.Symmetrize)
     )

shiftPairs = (R,k) -> (
     --assert(k==1); -- assume k=1
     n := numgens R-k;
     sImages := subsets(n+k, k);
     tImages := subsets(n, k);
     flatten apply(sImages, sImage->apply(tImages, tImage->(
		    sPos := 0;
		    tPos := 0;
		    sVars := new MutableList;
		    tVars := new MutableList;
		    for i from 0 to n+k-1 do
			 if      sPos < #sImage and sImage#sPos == i      then (sVars#(#sVars) = R_i; sPos = sPos+1)
			 else if tPos < #tImage and tImage#tPos == i-sPos then (tVars#(#tVars) = R_i; tPos = tPos+1)
			 else (sVars#(#sVars) = R_i; tVars#(#tVars) = R_i);
		    map(R,R, apply(k,j->0)|toList(sVars)),
		    map(R,R, apply(k,j->0)|toList(tVars))
		    )))
     )

symmetrize = method()
symmetrize List := F -> flatten (F/symmetrize)
symmetrize RingElement := f -> (
     R := ring f;
     supp'f := support f;
     apply(permutations gens R, p->
	  (map(R,R,p)) f
	  )
     )

interreduce = method(Options=>{Symmetrize=>true})
interreduce List := o -> F -> (
     print "-- starting \"slow\" interreduction";
     M := new MutableList from F;
     m := #F;
     local i;
     while( 
	   (i = position(0..m-1,i'-> 
		     any(m, j->j=!=i' and M#j != 0 and M#i'!= 0 and first gDivWitness(M#j,M#i'))
		     )     
	   ) =!= null  
     	  ) do (
	       M#i = makeMonic reduce(M#i,drop(M,{i,i})
		    --,Completely=>true
		    );
	       print toString (select(toList M, f->f!=0) / leadMonomial)
	  );
     M = toList select(M, f->f!=0);
     newF := apply(M, f->makeMonic(leadTerm f + reduce(f-leadTerm f,M,Completely=>true)));
     R := ring first newF;
     R' := R;
     if o.Symmetrize then R' = (coefficientRing R)[support ideal newF, MonomialOrder=>Lex]
     else (
	  firstVarPosition := position(gens R, x->(x == first support ideal newF));
	  R' = (coefficientRing R)[take(gens R, {firstVarPosition, numgens R - 1}), MonomialOrder=>Lex];
	  ); 
     apply(newF, f->sub(f,R'))
     ) 

-- should run faster if the reduction is done with the fast internal gb routine
-- ??? is there a function that just interreduces ???
interreduce'symmetrize = F -> ( 
     F' := flatten entries gens gb ideal symmetrize F;
     print F';
     time interreduce F'
     ) 

makeMonic = f -> if f== 0 then 0 else f/leadCoefficient f 

egb = method(Options=>{Symmetrize=>true})
egb (List) := o -> (F) -> (
     n := numgens ring first F;
     k := 0;
     while k < n do (
	  newF := processSpairs(F,k, Symmetrize => o.Symmetrize);
	  R := ring first F; 
	  R' := ring first newF; 
	  newstuff := numgens R != numgens R' or (
	       	  RtoR' := map(R',R, gens R'); 
		  sort apply(F,f->RtoR' f) != sort newF
		  );
	  print (k,sort F,sort newF,newstuff);
	  if newstuff and k > 1 then error "new stuff at k > 1";
	  if newstuff then k = 0 else k = k+1;
	  F = newF;
	  n = numgens ring first F;
	  );
     F
     )