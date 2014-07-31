simpleFactor = method(TypicalValue => MutableMatrix)
simpleFactor(RingElement) := (f) -> (
--name relevant objects    
    myRing = ring f;
--create output for predictable errors of input    
    if not isHomogeneous f
    then error "expected a polynomial ring over a field";
    myField = myRing.baseRings // last; --more efficient
    if not (isField myField)
    then error "expected a polynomial ring over a field";
    if (char R) =!= 0
    then error "expected a characteristic 0 base field";
--creating the new variables for the ring representing the enveloping algebra R**R
    numVars = length gens myRing;
    newGens = gens myRing;
    for i from 1 to numVars do (
    	newGens = append(newGens, y_i);
    ); 
    myNewRing = newRing(myRing, Variables=>newGens);
--collecting the x and y portions of the new varialbes, as elements of the new ring    
    XGens = {};
    YGens = {};
    for i from 1 to numVars do (
	XGens=append(XGens, (gens myNewRing)_(i-1));
	YGens=append(YGens, (gens myNewRing)_((numVars)+i-1));
    );	    
--constructing the copies of f(x) and f(y) in the new ring
    injX = map(myNewRing, myRing, matrix{XGens});
    injY = map(myNewRing, myRing, matrix{YGens});
    fx = injX(f);
    fy = injY(f);
--the placeholder for the coefficients of each (x_j-y_j)    
    coefficientMatrix = mutableMatrix(myNewRing, 1, numVars);
--make the matrix of differences x_i-y_i
    differenceMatrix = mutableMatrix(myNewRing,numVars,1);
    for i from 0 to (numVars-1) do (
	differenceMatrix_(i,0) = XGens_i-YGens_i);
    differenceMatrix = matrix differenceMatrix;
{*    remainderList = {(fx-fy)%differenceMatrix_(0,0)};
    for i from 1 to (numVars-1) do (
	remainderList = append(remainderList, (remainderList_(i-1))%differenceMatrix_(i,0))
	);
    coefficientMatrix_(0,0) = numerator((fx-fy-(fx-fy)%differenceMatrix_(0,0))/(differenceMatrix_(0,0)));    
    for i from 1 to (numVars-1) do (
	coefficientMatrix_(0,i) = numerator((remainderList_(i-1)-remainderList_i)/(differenceMatrix_(i,0)))
    );
(matrix coefficientMatrix, differenceMatrix) *}
(fx-fy)//gens (ideal differenceMatrix)
)

end
restart
load "simpleFactor.m2"
R = QQ[x_1,x_2]
f = x_1^2+x_1*x_2
A = simpleFactor(f)
(flatten entries ((transpose A)*differenceMatrix))_0==(fx-fy)


restart
load "simpleFactor.m2"
R = QQ[x_1..x_3]
f = x_3^2
A = simpleFactor(f)



restart
load "simpleFactor.m2"
R = QQ[x_1..x_10]
f = random(5,R)
A = simpleFactor(f)
(flatten entries ((transpose A)*differenceMatrix))_0==(fx-fy)


R = QQ[x_1,x_2,y_1,y_2]
f0 = x_1^2+x_1*x_2
g1 = x_1-y_1
g2 = x_2-y_2
h1 = (f0-(f0%g1))/(g1)
denominator h1
h1 = numerator h1
f1 = f0%g1
h2 = (f1-(f1%g2))/(g2)
h2 = numerator h2
