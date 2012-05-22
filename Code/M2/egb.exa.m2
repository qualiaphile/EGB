restart
load "egb.m2"
R = QQ[x_2,x_1,x_0, MonomialOrder => Lex]
F = {x_0^3*x_2+x_0^2*x_1^3, x_1^2*x_2^2-x_1^2*x_0+x_0*x_2^2};
F = processSpairs(F,1)
