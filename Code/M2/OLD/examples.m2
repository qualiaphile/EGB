exampleISSAC = ()->( -- problem 1.3 in ISSAC paper   
    R = buildERing({symbol x},{1},QQ,3);
    {x_0^3*x_2+x_0^2*x_1^3, x_1^2*x_2^2-x_1^2*x_0+x_0*x_2^2} 
    )
threeColoring = ()->(
    R = buildERing({symbol x,symbol y,symbol z},{1,1,1},QQ,2);
    {x_0^3 - 1, y_0^3 - 1, z_0^3 - 1, x_0^2 + x_0*y_1 + y_1^2, y_0^2 + y_0*z_1 + z_1^2, z_0^2 + z_0*x_1 + x_1^2}
    )
chrisAbraham = ()->(
    R = buildERing({symbol y,symbol x},{2,1},QQ,2);
    {y_(0,1) - x_0*x_1^2, y_(1,0) - x_0^2*x_1}
    )