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
export { egb, buildERing, Symmetrize }
protect \ { Completely, symbols, varIndices, varTable, varPosTable, semigroup, indexBound, diagonalSlices }
     
     
spoly = (f,g) -> (
     l := lcm(leadMonomial f,leadMonomial g);
     return (l//(leadTerm f))*f - (l//(leadTerm g))*g;
     )

-- In: v, a polynomial
--     w, a polynomial 
-- Out: (b, M)
--     b, a boolean, whether there is a semigroup element M s.t. M*in(v) divides in(w)
divWitness = (v,w) -> (
     R := ring v;
     n := R#indexBound;
     vl := (listForm leadTerm v)#0#0;
     wl := (listForm leadTerm w)#0#0;
     diag := (vl,b,i) -> vl#(R#varPosTable#((1:b)|(R#semigroup#b:i)));
     if all(R#semigroup, b->(b <= 1)) then (
     	  sigma := new MutableList from (n:-1);
     	  i := 0;
     	  for j from 0 to n-1 do (
	       if all(#(R#semigroup), b->(diag(vl,b,i) <= diag(wl,b,j))) then (
	       	    sigma#i = j;
	       	    i = i+1;
	       	    );
	       );
	  j := n;
     	  while i < n do (
	       if not all(#(R#semigroup), b->(diag(vl,b,i) == 0)) then return (false, {});
	       sigma#i = j;
	       i = i+1;
	       j = j+1;
	       );
     	  --print(v, w, sigma);
     	  return (true, toList sigma);
     	  )
     else (
	  sigma := new MutableList from (n:-1);
     	  i := 0;
	  while true do (
     	       for j from 0 to n-1 do (
	       	    if all(#(R#semigroup), b->(diag(vl,b,i) <= diag(wl,b,j))) then (
	       	    	 sigma#i = j;
	       	    	 i = i+1;
	       	    	 );
	       	    );
     	       while i < n do (
	       	    if not all(#(R#semigroup), b->(diag(vl,b,i) == 0)) then return (false, {});
	       	    i = i+1;
	       	    );
     	       --print(v, w, sigma);
     	       vlnew := (shiftMap(R,toList sigma)) v
	       );
	  );
     )

reduce = method(Options=>{Completely=>false})
reduce (RingElement, BasicList) := o -> (f,B) -> (
     B = select(toList B,b->b!=0);
     R := ring f;
     g:=f;
     divisible := true;
     while divisible and f != 0 do (
	  divisible = false;
	  local sigma; local divisor;
	  for b in B do (
	       (divisible, sigma) = divWitness(b,f);
	       if divisible then (
		    divisor = b;
		    break;
	       );
	  );
	  if divisible then (
	       sd := (shiftMap(R,sigma)) divisor;
	       f = f - (leadTerm f//leadTerm sd)*sd;
	       print("reduce:",g,f,divisor,sd);
	       );
	  );
     if not o.Completely or f == 0 then f
     else leadTerm f + reduce(f - leadTerm f,B,Completely=>true) 
     )

--In: X, a list of symbols to name each block of variables
--    s, a list of sequences of integers describing the action on each block of variables
--    K, a coefficient field
--    n, an integer
--Out: a polynomial ring over K with variable indices determined by s.
--     All "infinite" indices are included up to n-1. 
buildERing = method()
buildERing (Ring,ZZ) := (R,n) -> buildERing(R#symbols, R#semigroup, coefficientRing R, n)
buildERing (List,List,Ring,ZZ) := (X,s,K,n) -> (
     variableIndices := flatten apply(#s, b->(
	       toList (((1:b)|(s#b:0))..((1:b)|(s#b:n-1)))
	       ));
     R := K[reverse apply(variableIndices, i->(
		    if #i == 1 then X#(i#0)            --if block has only one variable, use no index
		    else if #i == 2 then X#(i#0)_(i#1) --if block has only one index, index by integers
		    else (X#(i#0))_(take(i,1-#i))      --if block has several indices, index by sequences
		    )), MonomialOrder => Lex];
     R#symbols = X;
     R#varIndices = reverse variableIndices;
     R#varTable = new HashTable from apply(#(R#varIndices), n->(R#varIndices#n => (gens R)#n));
     R#varPosTable = new HashTable from apply(#(R#varIndices), n->(R#varIndices#n => n));
     R#semigroup = s;
     R#indexBound = n;
     R
     )     

-- In: F, current generators list
--     k, ZZ (the number of "gaps")  
-- Out: the updated list of generators
-- Description: takes all s-pairs using k "gaps" when "interlacing", reduces, and interreduces. 
processSpairs = method(Options=>{Symmetrize=>true})
processSpairs (List,ZZ) := o -> (F,k) -> (
     if o.Symmetrize then F = interreduce'symmetrize F; 
     R := ring F#0;
     n := R#indexBound;
     S := buildERing(R,n+k);
     RtoS := map(S,R, apply(R#varIndices, i->S#varTable#i));
     F = F/RtoS;
     sp := shiftPairs(n,k);
     --print apply(sp,t->matrix first t||matrix last t);
     Fnew := {};
     for i from 0 to #F-1 do (
	  for j from 0 to i do (
	       for st in sp do (
		    (s,t) := st;
		    f := spoly((shiftMap(S,s)) F#i, (shiftMap(S,t)) F#j);
		    r := reduce(f,F);
		    --if f != 0 then print (i,j,s,t);
		    if r != 0 then (
			 << "(n)";
			 --print(F#i,F#j,r); 
			 Fnew = append(Fnew,r)
			 );
		    );
	       );
	  );
     interreduce(F|Fnew, Symmetrize => o.Symmetrize)
     )

-- In: n, ZZ
--     k, ZZ
-- Out: a List of all interlacing pairs of subsets of [n+k] of size n (with k gaps)
shiftPairs = (n,k) -> (
     --assert(k==1); -- assume k=1
     flatten apply(subsets(n+k,n), sImage->(
	       apply(subsets(sImage,n-k), stImage->(
			 sPos := 0;
			 stPos := 0;
			 tImage := select(n+k, i->(
				   sPos >= #sImage or i != sImage#sPos or (
					sPos = sPos+1;
					b := stPos < #stImage and i == stImage#stPos;
					if b then stPos = stPos+1;
					b
					)
				   ));
			 (sImage,tImage)
			 ))
	       ))			 
     )

--In: R, a ring
--    shift, a list of integers
--Out: a map from R to R where index i is mapped to shift#i.
--     If shift#i == -1 then all variables with index i go to 0_R.
shiftMap = (R,shift) -> (
     mapList := apply(R#varIndices, ind->(
	       indnew := new MutableList from ind;
	       for j from 1 to #ind-1 do (
		    if ind#j >= #shift or shift#(ind#j) < 0 or shift#(ind#j) >= R#indexBound then return 0_R
		    else indnew#j = shift#(ind#j);
		    );
	       R#varTable#(toSequence indnew)
	       ));
     map(R,R,mapList)
     )

-- In: F, a list of generators
-- Out: the symmetrization of F 
symmetrize = method()
symmetrize List := F -> flatten (F/symmetrize)
symmetrize RingElement := f -> (
     R := ring f;
     n := R#indexBound;
     apply(permutations toList (0..n-1), p->((shiftMap(R,p)) f))
     )

-- In: F, a list of generators
-- Out: ...
interreduce = method(Options=>{Symmetrize=>true})
interreduce (List) := o -> F -> (
     --Reduce elements of F with respect to each other.
     print "-- starting \"slow\" interreduction";
     M := new MutableList from F;
     while true do (
	  M = new MutableList from select(toList M, f->f!=0);
     	  i := position(0..(#M-1), k-> 
	       any(#M, j-> j != k and first divWitness(M#j,M#k)));
	  if i =!= null then M#i = makeMonic reduce(M#i,drop(M,{i,i}))
	  else break;
	  );
     M = toList M;
     newF := apply(M, f->makeMonic(leadTerm f + reduce(f-leadTerm f,M,Completely=>true)));
     --Prune unused variables from R.
     R := ring first newF;
     n := R#indexBound;
     vSupport := sum(apply(newF, f->sum(listForm(f)/first))); --list of # occurrances of each variable in newF
     nSupport := new MutableList from (n:0); --list of # occurances of each index value in variable support
     for i from 0 to #(R#varIndices)-1 do (
	  if vSupport#i > 0 then (
	       ind := R#varIndices#i;
	       for j from 1 to #ind-1 do nSupport#(ind#j) = nSupport#(ind#j)+1;
	       );
	  );
     newn := 0;
     if o.Symmetrize then (
	  shift := toList apply(nSupport, j->(if j > 0 then (newn = newn+1; newn-1) else -1));
	  newF = newF / shiftMap(R,shift);
	  )
     else for j from 0 to n-1 do if nSupport#j > 0 then newn = j+1;
     S := buildERing(R,newn);
     RtoS := map(S,R, apply(R#varIndices, i->(if S#varTable#? i then S#varTable#i else 0_S)));
     newF / RtoS
     ) 

-- should run faster if the reduction is done with the fast internal gb routine
-- ??? is there a function that just interreduces ???
interreduce'symmetrize = F -> ( 
     F' := flatten entries gens gb ideal symmetrize F;
     print F';
     time interreduce F'
     ) 

makeMonic = f -> if f== 0 then 0 else f/leadCoefficient f 

-- In:
-- Out: 
egb = method(Options=>{Symmetrize=>true})
egb (List) := o -> F -> (
     n := (ring first F)#indexBound;
     k := 0;
     while k < n do (
	  newF := processSpairs(F,k, Symmetrize => o.Symmetrize);
	  R := ring first F; 
	  S := ring first newF; 
	  newstuff := numgens R != numgens S or (
	       	  RtoS := map(S,R, apply(R#varIndices, i->(if S#varTable#? i then S#varTable#i else 0_S)));
		  sort (F / RtoS) != sort newF
		  );
	  print (k,sort newF,newstuff);
	  if newstuff then k = 0 else k = k+1;
	  F = newF;
	  n = S#indexBound;
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
     Key => {egb,(egb,List)},
     Headline => "computes equivariant Gröbner bases",
     Usage => "G = egb F",
     Inputs => {
          "F" => {"a list of polynomials over a field"}
          },
     Outputs => {
          "G" => {"An equivariant Gröbner basis for the equivariant ideal generated by F"}
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

undocumented {Symmetrize, buildERing, [egb,Symmetrize]}

TEST ///
needs concatenate(EquivariantGB#"source directory","./examples.m2")
I = exampleISSAC()
assert(toString egb I == toString {x_1*x_0^3, x_1^2*x_0^2, x_1^3*x_0, x_2*x_1*x_0^2, x_2*x_1^2-x_2*x_0^2, x_2^2*x_0-x_1^2*x_0, x_2^2*x_1-x_1*x_0^2})
///

end

restart
needsPackage "EquivariantGB"
help egb
check EquivariantGB
installPackage "EquivariantGB"

debug EquivariantGB
