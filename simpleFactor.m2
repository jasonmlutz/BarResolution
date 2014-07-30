simpleFactor = method(TypicalValue => MutableMatrix)
simpleFactor(RingElement) := (f) -> (
--name relevant objects    
    myRing := ring f;
--create output for predictable errors of input    
    if not isHomogeneous f
    then error "expected a polynomial ring over a field";
    myField := myRing.baseRings // last; --more efficient
    if not (isField myField)
    then error "expected a polynomial ring over a field";
    if (char R) =!= 0
    then error "expected a characteristic 0 base field";
--the list consisting of the (highest) degrees of each variable
    degreeList = buildDegreeList(f);    
--creating the new variables for the ring representing the enveloping algebra R**R
    numVars := length gens myRing;
    newGens = gens myRing;
    for i from 1 to numVars do (
    	newGens = append(newGens, y_i);
    ); 
    myNewRing := newRing(myRing, Variables=>newGens);
--collecting the x and y portions of the new varialbes, as elements of the new ring    
    XGens = {};
    YGens = {};
    for i from 1 to numVars do (
	XGens=append(XGens, (gens myNewRing)_(i-1));
	YGens=append(YGens, (gens myNewRing)_((numVars)+i-1));
    );	    
--constructing the copies of f(x) and f(y) in the new ring
    injX := map(myNewRing, myRing, matrix{XGens});
    injY := map(myNewRing, myRing, matrix{YGens});
    fx := injX(f);
    fy := injY(f);
    
    



end
restart
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
