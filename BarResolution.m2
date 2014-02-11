debuggingMode = true;
barResolution= method(TypicalValue => ChainComplex, Options => {LengthLimit => 2})
barResolution(PolynomialRing, Ideal):= opts -> (myRing,myIdeal) -> (
    myField := myRing.baseRings_((length myRing.baseRings) -1);
    if not (isField kk)
    then error "expected a polynomial ring over a field";
    barRes := new ChainComplex;
    numVars := length gens myRing;
    kAlg := myRing / myIdeal;
    envAlg := 
    --use vars(0..<2*(length gens myRing))
    --use apply to list and substitute to switch variables
    barRes        
)

envAlgRes = method(TypicalValue => Matrix)
envAlgRes(PolynomialRing, Ideal) := (myRing, myIdeal) -> (
--    myField := myRing.baseRings_((length myRing.baseRings) -1); -- pull the coefficient field
    myField := myRing.baseRings // last; --more efficient
    if not (isField myField)
    then error "expected a polynomial ring over a field";
    if not (char myField == 0)
    then error "expected a polynomial ring over a field of characteristic 0";
    if not (isHomogeneous myIdeal)
    then error "expected a homogeneous ideal of relations";
    numVars := length gens myRing;
    relsList := flatten entries gens myIdeal;
    numRelations := length relsList;
        --for ease, always generate ring by indexed variables x_1,..x_n
    newYVars := {};
    newZVars := {};
    for count from 1 to numVars do (
	newYVars = append(newVars, y_i)
	newZVars = append(newVars, z_i)
    );
    envAlg := myField[newYVars, newZVars];
    for i from 1 to numRelations do (
	f_i:= sub(relsList_i,matrix{newYVars})
	g_i:= sub(relsList_i,matrix{newZVars})
    );
    matrixForCycles := mutableMatrix(myEngAlg, numRelations, numGens);
    -- M2 treats a matrix in a resolution from R^n to R^m as having
    -- n rows and m columns
    
	
    
    
    ) --end of envAlgRes double input polyring and ideal

envAlgRes(QuotientRing) := (myQuotient) -> (
    myRing := ambient myQuotient;
    if not isPolynomialRing myRing
    then error "expected a quotient of a polynomial ring";
    myIdeal := ideal myQuotient;
    envAlgRes(myRing, myIdeal)
    ) -- endof envAlvRes for quotients
    

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

