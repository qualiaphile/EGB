R.<x> = InfinitePolynomialRing(QQ)
I = R.ideal([x[1]*x[2] + x[3]])
I = R.ideal([x[1]^3*x[3]+x[1]^2*x[2]^3, x[2]^2*x[3]^2-x[2]^2*x[1]+x[1]*x[3]^2])
G = R*I.groebner_basis()
Q = R.quotient(G)
p = x[3]*x[1]+x[2]^2+3
Q(p)*x[2] == Q(p)*x[1]*x[3]*x[5]


