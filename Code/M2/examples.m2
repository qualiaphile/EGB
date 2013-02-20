exampleISSAC = ()->( -- problem 1.3 in ISSAC paper   
    QQ[x_2,x_1,x_0, MonomialOrder => Lex];
    {x_0^3*x_2+x_0^2*x_1^3, x_1^2*x_2^2-x_1^2*x_0+x_0*x_2^2} 
    )
threeColoring = ()->(
    QQ[reverse(x_(0,0)..x_(1,2)),MonomialOrder=>Lex];
    {x_(0,0)^3 - 1, x_(0,1)^3 - 1, x_(0,2)^3 - 1, x_(0,0)^2 + x_(0,0)*x_(1,1) + x_(1,1)^2, x_(0,1)^2 + x_(0,1)*x_(1,2) + x_(1,2)^2, x_(0,2)^2 + x_(0,2)*x_(1,0) + x_(1,0)^2}
    )
