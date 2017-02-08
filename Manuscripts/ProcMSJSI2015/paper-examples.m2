-- Computational Examples
restart
needsPackage "EquivariantGB"
R = buildERing({symbol x, symbol y}, {1,2}, QQ, 2);

-- finishes
egb({y_(0,0) - x_0^2, y_(1,0) - x_1*x_0, y_(0,1) - x_0*x_1}, Algorithm=>Incremental)

-- finishes
egb({y_(0,1) - x_0^2*x_1, y_(1,0) - x_1^2*x_0}, Algorithm=>Incremental)

restart
needsPackage "EquivariantGB"
R = buildERing({symbol x}, {1}, QQ, 6);
h = x_0*x_4^2+x_0*x_1^2+x_1*x_0^2-2*x_1*x_0+x_0*x_3*x_4-x_0*x_5^2-x_0*x_3*x_5-2*x_1^2
G = egb({x_0*x_1 - x_1*x_2^2 + x_1^2}, Algorithm=>Incremental)
reduce(h, G)
