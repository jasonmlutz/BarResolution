cleverFactor = method()
cleverFactor := (f) -> (
    myRing := ring f;
    if not isHomogeneous f
    then error "expected a polynomial ring over a field";
    myField := myRing.baseRings // last; --more efficient
    if not (isField myField)
    then error "expected a polynomial ring over a field";
    if (char R) =!= 0
    then error "expected a characteristic 0 base field";
    numVars := length gens myRing;
    newGens = gens myRing;
    for i from 1 to numVars do (
    	newGens = append(newGens, y_i);
    );
    myNewRing := newRing(myRing, Variables=>newGens);
    XGens = {};
    YGens = {};
    for i from 1 to numVars do (
	XGens=append(XGens, (gens myNewRing)_(i-1));
	YGens=append(YGens, (gens myNewRing)_((numVars)+i-1));
    );	    
    injX := map(myNewRing, myRing, matrix{XGens});
    injY := map(myNewRing, myRing, matrix{YGens});
    fx := injX(f);
    fy := injY(f);
    deg := degree f;

    
)


end
restart
load "cleverFactor.m2"
R = QQ[x_1,x_2]
f = x_1^2+x_1*x_2
