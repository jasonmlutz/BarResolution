debuggingMode = true;
barResolution= method(TypicalValue => ChainComplex, Options => {LengthLimit => 2})
barResolution(PolynomialRing, Ideal):= opts -> (myRing,myIdeal) -> (
    myField := myRing.baseRings_((length myRing.baseRings) -1);
    if not (isField kk)
    then error "expected a polynomial ring over a field";
    barRes := new ChainComplex;
    numVars := length gens myRing;
    envAlg := 
    --use vars(0..<2*(length gens myRing))
    barRes        
)
end
--test code here
restart
load "BarResolution.m2"
-- test with correct naming conventions
myRing = QQ[x_1,x_2]
myIdeal = ideal((x_1)^3,x_1*x_2)
barResolution(myRing,myIdeal)
--motivating example
R = QQ[x_1,x_2]
S = QQ[y_1,y_2,z_1,z_2]
I = ideal((y_1)^3, y_1*y_2)
J = ideal((z_1)^3, z_1*z_2)
T= S/(I+J)
f_0 = map(R, T, matrix{{x_1,x_2,x_1,x_2}})
K_1 = kernel f_0
K_1 = kernel f_0
M_1 = matrix{entries (gens K_1)_0}++matrix{entries (gens K_1)_1}
f_1 = map(module K_1, T^(length flatten entries gens K_1), M_1)
K_2 = kernel f_1

