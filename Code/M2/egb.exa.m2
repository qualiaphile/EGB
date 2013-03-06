restart
needsPackage "EquivariantGB"
load "examples.m2"

F = exampleISSAC()
-- (x_3*x_1^3 + x_2^3*x_1^2, x_3^2*x_2^2 + x_3^2*x_1 - x_2^2*x_1) -- sage input
-- (x_2*x_1^2, x_2^2*x_1) -- sage output
F = {x_2*x_1*x_0^2, x_2^2*x_0-x_1^2*x_0, x_1*x_0^3, x_1^2*x_0^2} -- simplified ISSAC paper answer (example 1.7)

-- various stuff... 
F = {x_2*x_1*x_0 + x_1*x_0};
F = {x_1*x_0+x_2*x_1+x_2*x_0};
F = {random(2,R)+random(1,R)}
R = QQ[x_3,x_2,x_1,x_0, MonomialOrder => Lex]
F = {x_2*x_1, x_3*x_0+x_0^2} -- example for new stuff at k=2

restart
needsPackage "EquivariantGB"
R = buildERing({symbol x},{1}, QQ, 3)
F = {x_2^1*x_0^1, x_2^2 + x_2^1*x_1}                             -- G-basis in 4 variables
F = {x_2^2*x_0^2, x_2^4 + x_2^3*x_1 + x_2^2*x_1^2}               -- G-basis in 5 variables
F = {x_2^3*x_0^3, x_2^6 + x_2^5*x_1 + x_2^4*x_1^2 + x_2^3*x_1^3} -- G-basis in 6 variables
F = {x_2^4*x_0^4, x_2^8 + x_2^7*x_1 + x_2^6*x_1^2 + x_2^5*x_1^3 + x_2^4*x_1^4}
F = {x_2^5*x_0^5, x_2^10+ x_2^9*x_1 + x_2^8*x_1^2 + x_2^7*x_1^3 + x_2^6*x_1^4 + x_2^5*x_1^5}
F = {x_2^3*x_0^3, x_2^6 + x_2^5*x_1 + x_2^4*x_1^2}
egb(F,Symmetrize=>false)

R = QQ[x_1,x_0, MonomialOrder => Lex]
F = {x_0^2 - x_0*x_1 + x_1^2}
F = {x_1^3 + x_1^2*x_0 + x_1*x_0^2}
F = {(x_1 + x_0)^3}

egb F                     -- Symmetrize => true : at every step the set of generators is symmetrized
egb(interreduce'symmetrize F,Symmetrize=>false) -- symmetrization at the first step ONLY
egb(F,Symmetrize=>false)                        -- no symmetrization, a G-basis of F is computed, where G=Inc(N)

restart
needsPackage "EquivariantGB"
R = buildERing({symbol x,symbol y,symbol z},{1,1,1}, QQ, 2)
F = {x_0^3 - 1, y_0^3 - 1, z_0^3 - 1, x_0^2 + x_0*y_1 + y_1^2, y_0^2 + y_0*z_1 + z_1^2, z_0^2 + z_0*x_1 + x_1^2}
egb(F,Symmetrize=>false)
debug EquivariantGB
interreduce F

F = symmetrize F
F = interreduce symmetrize F
F = interreduce'symmetrize F
F = interreduce symmetrize interreduce symmetrize F
F = processSpairs(F,0) -- tries to find an S-basis (a G-basis for the S-ideal)
F = processSpairs(F,1) -- tries to find an S-basis (a G-basis for the S-ideal)
F = processSpairs(F,2) -- tries to find an S-basis (a G-basis for the S-ideal)
F = processSpairs(F,3) -- tries to find an S-basis (a G-basis for the S-ideal)
F = processSpairs(F,0,Symmetrize=>false) -- tries to find the G-basis
F = processSpairs(F,1,Symmetrize=>false) -- tries to find the G-basis
F = processSpairs(F,2,Symmetrize=>false) -- tries to find the G-basis
F = processSpairs(F,3,Symmetrize=>false) -- tries to find the G-basis


-- m-minors of an m by n matrix with "shifted rows"
FF = QQ
FF = ZZ/101
n = 3
m = 3
R = FF[reverse(x_0..x_(n+m-2)), MonomialOrder => Lex]
F = {det matrix apply(m, i->take(gens R,{i,i+n-1}))}
