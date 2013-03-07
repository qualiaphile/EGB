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
     assert(numgens ring v == numgens ring w);
     n := R#indexBound;
     vl := (listForm leadTerm v)#0#0;
     wl := (listForm leadTerm w)#0#0;
     diag := (vl,b,i) -> vl#(R#varPosTable#((1:b)|(R#semigroup#b:i)));
     vmax := position(indexSupport({leadTerm v}), i->(i > 0), Reverse=>true);
     wmax := position(indexSupport({leadTerm w}), i->(i > 0), Reverse=>true);
     sigma := new MutableList from (n:-1);
     k := 0;
     while true do (
	  while true do (
	       i := k;
	       for j from (sigma#k)+1 to wmax do (
		    if all(#(R#semigroup), b->(diag(vl,b,i) <= diag(wl,b,j))) then (
			 sigma#i = j;
			 i = i+1;
			 );
		    );
	       if i <= vmax then k = k-1 else break;
	       if k < 0 then return (false, {});
	       );
	  for i from vmax+1 to n-1 do sigma#i = sigma#vmax + i - vmax;
	  if all(R#varIndices, ind->(
		    sind := (1:ind#0)|apply(1..#ind-1, j->sigma#(ind#j));
		    (not R#varPosTable#? sind and vl#(R#varPosTable#ind) == 0)
		    or vl#(R#varPosTable#ind) <= wl#(R#varPosTable#sind))) 
		    then break;
	  k = vmax;
	  );
     return (true, toList sigma);
     )

reduce = method(Options=>{Completely=>false})
reduce (RingElement, BasicList) := o -> (f,B) -> (
     B = select(toList B,b->b!=0);
     R := ring f;
     n := R#indexBound;
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
	       iS := indexSupport({divisor});
	       maxi := position(iS, i->(i != 0), Reverse=>true);
	       if sigma#maxi >= n then return null;
	       sd := (shiftMap(R,sigma)) divisor;
	       f = f - (leadTerm f//leadTerm sd)*sd;
	       --print("reduce:",g,f,divisor,sd);
	       );
	  );
     if not o.Completely or f == 0 then f
     else leadTerm f + reduce(f - leadTerm f,B,Completely=>true) 
     )

--runs reduce, but possibly expands the ring in the process
reduce2 = method(Options=>{Completely=>false})
reduce2 (RingElement,List) := o -> (f,F) -> (
     R := ring f;
     r := reduce(f,F,Completely=>o.Completely);
     while r === null do (
     	  Rnew := buildERing(R,(R#indexBound)+1);
     	  RtoRnew := ringMap(Rnew,R);
     	  F = RtoRnew\F;
     	  f = RtoRnew f;
     	  r = reduce(f,F,Completely=>o.Completely);
	  R = Rnew
	  );
     (r,R,f,F)
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
     F = F / ringMap(S,R);
     sp := shiftPairs(n,k);
     --print apply(sp,t->matrix first t||matrix last t);
     Fnew := {};
     for i from 0 to #F-1 do (
	  for j from 0 to i do (
	       for st in sp do (
		    (s,t) := st;
		    f := spoly((shiftMap(S,s)) F#i, (shiftMap(S,t)) F#j);
		    local r;
		    (r,S,f,F) = reduce2(f,F);
		    --if f != 0 then print (i,j,s,t);
		    if r != 0 then (
			 << "(n)";
			 --print(F#i,F#j,r); 
			 Fnew = append(Fnew,r)
			 );
		    );
	       );
	  );
     Fnew = apply(Fnew, f->((ringMap(S,ring f)) f));
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

ringMap = (S,R) -> map(S,R, apply(R#varIndices, i->(if S#varTable#? i then S#varTable#i else 0_S)))

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
     R := ring first F;
     n := R#indexBound;
     while true do (
	  F = select(F, f->f!=0);
     	  i := position(0..#F-1, k-> 
	       any(#F, j-> j != k and first divWitness(F#j,F#k)));
	  if i =!= null then (
	       Fout := drop(F,{i,i});
	       local r; local f;
	       (r,R,f,Fout) = reduce2(F#i,Fout);
	       F = insert(i, makeMonic r, Fout);
	       )
	  else break;
	  );
     F = apply(#F, i->(
	       g := F#i - leadTerm(F#i);
	       local r;
	       (r,R,g,F) = reduce2(g,F,Completely=>true);
	       makeMonic(leadTerm(F#i) + r)
	       ));
     --Prune unused variables from R.
     iS := indexSupport F;
     newn := 0;
     if o.Symmetrize then (
	  shift := toList apply(iS, j->(if j > 0 then (newn = newn+1; newn-1) else -1));
	  F = F / shiftMap(R,shift);
	  )
     else newn = position(iS, i->(i > 0), Reverse=>true) + 1;
     S := buildERing(R,newn);
     F / ringMap(S,R)
     ) 

--In: F, a list of polynomials
--Out: a list, the number of variables represented in F which have an index equal to i for each i from 0 to n-1
indexSupport = F -> (
     R := ring first F;
     n := R#indexBound;
     vSupport := sum(apply(F, f->sum(listForm(f)/first))); --list of # occurrances of each variable in newF
     nSupport := new MutableList from (n:0); --list of # occurances of each index value in variable support
     for i from 0 to #(R#varIndices)-1 do (
	  if vSupport#i > 0 then (
	       ind := R#varIndices#i;
	       for j from 1 to #ind-1 do nSupport#(ind#j) = nSupport#(ind#j)+1;
	       );
	  );
     toList nSupport
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
	  newstuff := numgens R != numgens S or sort (F / ringMap(S,R)) != sort newF;
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
