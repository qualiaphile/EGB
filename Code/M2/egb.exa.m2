
-- problem 1.3 in ISSAC paper   
restart
load "egb.m2"
R = QQ[x_2,x_1,x_0, MonomialOrder => Lex]
F = {x_0^3*x_2+x_0^2*x_1^3, x_1^2*x_2^2-x_1^2*x_0+x_0*x_2^2};
F = processSpairs(F,1)
F = processSpairs(F,1,Symmetrize=>false)


--------------------------------

load "egb.m2"
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


