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

envAlgRes = method(TypicalValue => MutableMatrix, 
    Options => {Rigorous => false, QuotientSource => false, NaiveStrategy=>true})
envAlgRes(PolynomialRing, Ideal) := opts-> (myRing, myIdeal) -> (
--    myField := myRing.baseRings_((length myRing.baseRings) -1); -- pull the coefficient field
    myField := myRing.baseRings // last; --more efficient
    numVars := length gens myRing;
    if opts.QuotientSource
    then print "WARNING: ensure variables are x_1..x_n for accuracy"
    else (
    varTest := true;
    for i from 1 to numVars do (
	varTest = (varTest and ((gens myRing)_(i-1)===x_i))
    );
    if not varTest
    then print "WARNING: expected variables x_1..x_n";
    );
    if opts.Rigorous
    then (
        if not (isField myField)
	then print "WARNING: expected a polynomial ring over a field";
	if not (char myField == 0)
	then print "WARNING: expected a polynomial ring over a field of characteristic 0";
	if not (isHomogeneous myIdeal)
	then print "WARNING: expected a homogeneous ideal of relations";
    );
    relsList := flatten entries gens myIdeal;
    numRelations := length relsList;
        --for ease, always generate ring by indexed variables x_1,..x_n
    newYVars = {};
    newZVars = {};	
    for i from 1 to numVars do (
    	newYVars = append(newYVars, y_i);
	newZVars = append(newZVars, z_i);
	);
    YRing := myField[newYVars];
    ZRing := myField[newZVars];
    myEnvAlg := myField[newYVars, newZVars];
    YGens := {};
    ZGens := {};
    for i from 1 to numVars do (
	YGens=append(YGens, (gens myEnvAlg)_(i-1));
	ZGens=append(ZGens, (gens myEnvAlg)_((numVars)+i-1));
    );	    
    injY := map(myEnvAlg, myRing, matrix{YGens});
    injZ := map(myEnvAlg, myRing, matrix{ZGens});
    for i from 1 to numRelations do (
--	f_i= sub(relsList_(i-1),matrix{newYVars});
--	h_i= sub(relsList_(i-1),matrix{newZVars})
    	f_i = injY(relsList_(i-1));
    	h_i = injZ(relsList_(i-1));	
    );
--    matrixForCycles := mutableMatrix(myEngAlg, nrows=rank target, ncols=rank source);
    matrixForCycles := mutableMatrix(myEnvAlg, numVars, numRelations);
    -- M2 treats a matrix in a resolution from R^n to R^m as having
    -- n columns and m rows
    -- indexing of rows and columns starts at zero.
    varDiff :={};
    for i from 1 to numVars do (
	varDiff = append(varDiff, y_i-z_i)
    );
--start of syzygy strategy
    if opts.NaiveStrategy == false then (
    matrixForCycles = mutableMatrix(myEnvAlg, numVars, numRelations);
    for j from 1 to numRelations do (
	tempVarDiff = append(varDiff, f_j-h_j);
	syzSource = matrix{{tempVarDiff}};
	tempKernel = kernel syzSource;
	
	
	--include fail check to force naive strategy
    ) --end of syzygy strategy    
--start of naive strategy    
    if (SyzygyStrategyFail or opts.NaiveStrategy) then (
    matrixForCycles = mutableMatrix(myEnvAlg, numVars, numRelations); --clears entries
    for j from 1 to numRelations do (
	dividendHold = f_j-h_j;
    for i from 1 to numVars do (
	entryHold = (dividendHold - (dividendHold)%(y_i-z_i))/(y_i-z_i);
	if not (isUnit denominator entryHold)
	then error ("non-unit denominator in stage j=",toString j, "and i=", toString i);
	print(denominator entryHold);
--    	matrixForCycles_(i-1,j-1) = (numerator entryHold)*(1/(denominator entryHold));
    	matrixForCycles_(i-1,j-1) = (numerator entryHold);
	dividendHold = dividendHold - (numerator entryHold)*(y_i-z_i);
	);
    );
    );
    --sanity check
--    if opts.Rigorous then (
    varMatrix := matrix{varDiff};
    testMatrix := varMatrix*matrix(matrixForCycles);
    for j from 1 to numRelations do (
--	sanityCheck := sum(numVars-1, i -> matrixForCycles_(i,j-1)*(y_(i+1)-z_(i+1)));
--	if not (sanityCheck == f_j-h_j)
--    then error ("incorrect sum check of coefficients in column ",toString (j));	
--    print(j, sanityCheck == f_j-h_j);
    if not (testMatrix_(0,j-1) == f_j-h_j)
    then print ("WARNING: incorrect sum check of coefficients in column ",toString (j));
	);
--    );
    matrixForCycles
    ) --end of envAlgRes with inputs polynomial ring and ideal

----
-- New technique to implement: manually build a matrix {{y_1-z_1,..,y_n-z_n,f_j}} and 
-- find a column in the presentation of the kernel which has 1 in the last enter.
----

envAlgRes(QuotientRing) := opts -> (myQuotient) -> (
    myRing := ambient myQuotient;
    if opts.Rigorous then (
    if not isPolynomialRing myRing
    then print "WARNING: expected a quotient of a polynomial ring";
    );
    myIdeal := ideal myQuotient;
    envAlgRes(myRing, myIdeal, QuotientSource => true)
    ) -- endof envAlvRes for quotients
    

end
--test code here
restart
load "BarResolution.m2"
--test for envAlgRes
R = QQ[x_1,x_2, y_1,y_2]
I = ideal((x_1)^3,x_1*x_2)
M = envAlgRes(R, I)
S = R/I
N = envAlgRes(S)
--assert((matrix M) == (matrix N)) --doesn't work, targets aren't ===

R = QQ[x_1,x_2,x_3]
I = ideal((x_1)^3+(x_3)^3, x_1*x_2-x_2^2, x_2^4-x_1*x_2*x_3^2+3*x_2^3*x_3)
M = envAlgRes(R,I, Rigorous => true)
--class of random examples, doesn't work
n = 2 --numVars
c = 3 --numRelations
R = QQ[x_1..x_n]
--T = ZZ[x_1..x_n]
--f = map(R, T, matrix{gens R})
gensList = ()
for i from 1 to c do (
      gensList = append(gensList, random(2+(-1)^i,R)))
I = ideal(gensList)
M = envAlgRes(R, I, Rigorous => true)  

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
