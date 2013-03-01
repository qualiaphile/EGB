newPackage(
     "EquivariantGB",
     Version =>"0.1",
     Date => "2013",
     Headline => "Equivariant Groebner bases and related algorithms",
     HomePage => "",
     Authors => {
    	  {Name => "Chris Hillar", Email => "chillar@msri.org"},
	  {Name => "Robert Krone", Email => "krone@math.gatech.edu"},
	  {Name => "Anton Leykin", Email => "leykin@math.gatech.edu"}
	  },
     -- DebuggingMode should be true while developing a package, 
     --   but false after it is done
     DebuggingMode => true 
     )
export { egb, interreduce'symmetrize, Symmetrize }
protect Completely

spoly = (f,g) -> (
     l := lcm(leadMonomial f,leadMonomial g);
     return (l//(leadTerm f))*f - (l//(leadTerm g))*g;
     )

gmDivWitness = (v,w,m) -> (
     R := ring v;
     n := (numgens R)//m;
     v = reverse (listForm leadTerm v)#0#0;
     w = reverse (listForm leadTerm w)#0#0;
     sigma := new MutableList from (n:-1);
     i := 0;
     for j from 0 to n-1 do
	  if all(m, k->(v#(i*m+k) <= w#(j*m+k))) then (sigma#i = n-1-j; i = i+1);
     for j from i*m to (n*m-1) do
	  if v#j != 0 then return (false, {});
     --print(v,w,toList sigma);
     sigma = reverse sigma;
     sVars := flatten toList apply(sigma, i-> apply(m,j->(if i < 0 then 0 else R_(m*i + j))));
     return (true, map(R,R, toList(sVars)));
     )

reduce = method(Options=>{Completely=>false})
reduce (RingElement, BasicList) := o -> (f,B) -> reduce(f,B,1,Completely=>o.Completely)
reduce (RingElement, BasicList, ZZ) := o -> (f,B,m) -> (
     B' := select(toList B,b->b!=0);
     R := ring f;
     divisionOccured := true;
     while divisionOccured and f != 0 do (
	  local divisible; local sigma;
	  divisors := select(1, B', b->(
		    (divisible, sigma) = gmDivWitness(b,f,m);
		    divisible
		    ));
	  if #divisors>0 then (
	       sb := sigma(first divisors);
	       --print(f,first divisors, sb);
	       f = f - (leadTerm f//leadTerm sb)*sb;
	       )
	  else divisionOccured = false;
	  );
     if not o.Completely or f == 0 then f
     else leadTerm f + reduce(f - leadTerm f,B',m,Completely=>true) 
     )
			 

processSpairs = method(Options=>{Symmetrize=>true})
processSpairs (List,ZZ,ZZ) := o -> (F,k,m) -> (
     if o.Symmetrize then F = interreduce'symmetrize F; 
     R := ring F#0;
     n := ceiling((numgens R)/m);
     x := symbol x;
     R' := if m == 1 then (coefficientRing R)[reverse(x_0..x_(n+k-1)), MonomialOrder => Lex]
     	  else (coefficientRing R)[reverse(x_(0,0)..x_(n+k-1,m-1)), MonomialOrder => Lex];
     RtoR' := map(R',R, drop(gens R',(numgens R')-(numgens R)));
     F = F/RtoR';
     sp := shiftPairs(R',k,m);
     --print apply(sp,t->matrix first t||matrix last t);
     nF := #F;
     F' := {};
     scan(nF, i->
	  scan(i+1, j->(
		    --if i!=j then
		    for st in sp do (
		    	 (s,t) := st;
		    	 f := spoly(s F#i, t F#j);
		    	 r := reduce(f,F,m);
		    	 --if f != 0 then print (i,j,s,t);
		    	 if r != 0 then (
			      << "(n)"; 
			      -- if i==j then print(F#i,F#j,r,matrix s,matrix t);
			      F' = append(F',r)
			      );
		    	 );
	       	    ))
	  );
     interreduce(F|F',m, Symmetrize => o.Symmetrize)
     )

shiftPairs = (R,k,m) -> (
     --assert(k==1); -- assume k=1
     n := (numgens R)//m -k;
     sImages := subsets(n+k, k);
     tImages := subsets(n, k);
     flatten apply(sImages, sImage->apply(tImages, tImage->(
		    sPos := 0;
		    tPos := 0;
		    sVars := new MutableList;
		    tVars := new MutableList;
		    for i from 0 to n+k-1 do
			 if      sPos < #sImage and sImage#sPos == i      then (sVars#(#sVars) = i; sPos = sPos+1)
			 else if tPos < #tImage and tImage#tPos == i-sPos then (tVars#(#tVars) = i; tPos = tPos+1)
			 else (sVars#(#sVars) = i; tVars#(#tVars) = i);
		    sVars = flatten toList apply(sVars, i-> apply(m,j->R_(m*i + j)));
		    tVars = flatten toList apply(tVars, i-> apply(m,j->R_(m*i + j)));
		    map(R,R, apply(k*m,j->0)|toList(sVars)),
		    map(R,R, apply(k*m,j->0)|toList(tVars))
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
interreduce List := o -> F -> interreduce(F,1,Symmetrize=>o.Symmetrize)
interreduce (List,ZZ) := o -> (F,m) -> (
     print "-- starting \"slow\" interreduction";
     M := new MutableList from F;
     while true do (
	  M = new MutableList from select(toList M, f->f!=0);
     	  i := position(0..(#M-1), k-> 
	       any(#M, j-> j != k and first gmDivWitness(M#j,M#k,m)));
	  if i =!= null then M#i = makeMonic reduce(M#i,drop(M,{i,i}),m)
	  else break;
	  );
     M = toList M;
     newF := apply(M, f->makeMonic(leadTerm f + reduce(f-leadTerm f,M,m,Completely=>true)));
     R := ring first newF;
     R' := R;
     if o.Symmetrize then R' = (coefficientRing R)[support ideal newF, MonomialOrder=>Lex]
     else (
	  firstVarPosition := numgens R;
	  if #(support ideal newF) > 0 then firstVarPosition = (index first support ideal newF)//m;
	  R' = (coefficientRing R)[take(gens R, {firstVarPosition*m, numgens R - 1}), MonomialOrder=>Lex];
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
egb (List) := o -> (F) -> egb(F,1,Symmetrize=>o.Symmetrize)
egb (List,ZZ) := o -> (F,m) -> (
     if (m != 1 and o.Symmetrize) then error "not supported";
     n := (numgens ring first F)//m;
     k := 0;
     while k < n do (
	  newF := processSpairs(F,k,m, Symmetrize => o.Symmetrize);
	  R := ring first F; 
	  R' := ring first newF; 
	  newstuff := numgens R != numgens R' or (
	       	  RtoR' := map(R',R, gens R'); 
		  sort apply(F,f->RtoR' f) != sort newF
		  );
	  print (k,sort newF,newstuff);
	  --if newstuff and k > 1 then error "new stuff at k > 1";
	  if newstuff then k = 0 else k = k+1;
	  F = newF;
	  n = (numgens ring first F)//m;
	  );
     F
     )

beginDocumentation()

document {
     Key => EquivariantGB,
     Headline => "a package for computing equivariant Gröbner bases",
     "There can be explanatory prose here in the form of a hypertext list.",
     EXAMPLE {
          "m2code",
          "m2code",
          "m2code"
          },
     "There can be explanatory prose here in the form of a hypertext list.",
     Subnodes => {
          TO egb
          }
     }

document {
     Key => egb,
     Headline => "computes equivariant Gröbner bases",
     Usage => {
	  "egb F",
	  "egb(F,m)"
	  },
     Inputs => {
          "F" => {"a list of polynomials over a field"},
	  "m" => {"an integer"}
          },
     Outputs => {
          "An equivariant Gröbner basis for the equivariant ideal generated by F"
          },
     Consequences => {
          -- each effect is a hypertext list
          },
     "There can be explanatory prose here in the form of a hypertext list.",
     EXAMPLE {
          "m2code",
          "m2code",
          "m2code"
          },
     "There can be explanatory prose here in the form of a hypertext list.",
     Caveat => {"warning"}
     }

undocumented {egb,Symmetrize}

TEST ///
needs concatenate(EquivariantGB#"source directory","./examples.m2")
I = exampleISSAC()
assert(toString egb I == toString {x_1*x_0^3, x_1^2*x_0^2, x_1^3*x_0, x_2*x_1*x_0^2, x_2*x_1^2-x_2*x_0^2, x_2^2*x_0-x_1^2*x_0, x_2^2*x_1-x_1*x_0^2})
///

end

restart
needsPackage "EquivariantGB"
check EquivariantGB

