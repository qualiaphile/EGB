needsPackage "EquivariantGB"
load "examples.m2"
R = buildERing({symbol y,symbol x},{2,1}, QQ, 2)
F = {y_(1,0) - x_1*x_0}
egb(F,Symmetrize=>false)
quit
