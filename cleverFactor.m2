--the method for building the lists of powers outside of the cleverFactor method
listBuilder = method()
listBuilder(List,ZZ) := (degreeList,deg) -> (
    finished = false;
    listOfPowers = {};
    for i from 0 to (#degreeList-1) do (
	listOfPowers = append(listOfPowers, 0)
	);
    	listOfLists = {};
    while finished == false do (
	if (sum(listOfPowers) < deg)
	then (
	    listOfLists = append(listOfLists,listOfPowers)
	    );
	overflowColumn = 0;
	activateOverflow = false;
	if (listOfPowers_0 >= (degreeList_0)) 
	then (
	    activateOverflow = true;
	);
	if activateOverflow == false 
	then (
	    tempList = {(listOfPowers_0)+1};
	    for i from 1 to (#listOfPowers-1) do (
		tempList = append(tempList, listOfPowers_i)
		);
	    listOfPowers = tempList;
	    )
	else (
	    overflowLocated = false;
	    while overflowLocated == false do (
		overflowColumn = overflowColumn +1;
		if (overflowColumn >= #listOfPowers) then (overflowLocated = true; finished = true;)
		else(
		    if (listOfPowers_overflowColumn < degreeList_overflowColumn) then (
		    overflowLocated = true)
		);
	    );
	    if (overflowColumn < #listOfPowers) then (
		tempList = {};
		for i from 0 to (overflowColumn-1) do (
		    tempList = append(tempList,0)
		    );
		tempList = append(tempList, (listOfPowers_overflowColumn)+1);
		for i from (overflowColumn+1) to (#listOfPowers-1) do (
		    tempList = append(tempList, listOfPowers_i)
		);
	    	listOfPowers = tempList;
	    );
	);
    );
listOfLists
)

--performs partial derivatives of the given polynomial by
--the variables in the given list
specialPartial = (myPolynomial,powersList, variablesList,bonus) -> (
    if not (#powersList == #variablesList) then error "expected two lists of same size";
    myRing = ring myPolynomial;
    if not (isSubset(variablesList, gens myRing)) then error "expected argument 3 to be a subset of the generators of the ring";
    diffed = myPolynomial;
    for i from 0 to (#powersList-1) do (    
	for j from 1 to (powersList_i) do (
	diffed = diff(variablesList_i,diffed)
	);
    );
    diff(variablesList_(bonus-1),diffed)
)--works!

--build a list consisting of the highest power
--of each variable appearing
buildDegreeList = (myPolynomial) -> (
    degreeList = {};
    myRing = ring myPolynomial;
    for i from 1 to #gens(myRing) do (
        degreeList = append(degreeList,degree((gens R)_(i-1),myPolynomial));
    );
    degreeList
)--works!        

factorial = i -> (
    i!
)

incrementList = (myList,bonus) -> (
    tempList = {};
    for i from 0 to (bonus-2) do (
	tempList = append(tempList,myList_i)
	);
    tempList = append(tempList, (myList_(bonus-1)+1));
    for i from (bonus) to (#myList-1) do (
	tempList = append(tempList, myList_i)
    );        
tempList
)

--compute the monomial corresponding to degrees of the variables
varsPowers = (myList,myVars) -> (
    holder = 1;
    for i from 0 to (#myList -1) do (
	holder = holder*(myVars_i)^(myList_i);
    );
    holder	
)            


cleverFactor = method(TypicalValue => MutableMatrix)
cleverFactor(RingElement) := (f) -> (
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
    deg := first (degree f);
--the placeholder for the coefficients of each (x_j-y_j)    
    coefficientMatrix = mutableMatrix(myNewRing, 1, numVars);
--create and populate a list to track the exponents
    listOfPowers = {};
    for i from 1 to numVars do (
	listOfPowers = append(listOfPowers, 0);
    );
--call to listBuilder to created the list of powers
    listOfLists = listBuilder(degreeList,deg);
    for listOfPowers in listOfLists do (
	
    	for columnCount from 1 to numVars do (
--for each j, the general algorithm sums over these multisets that contain j.
--to make the above construction apply independently of j, the multisets above
--were allowed to have, at most, deg-1 terms, so that one more y_j can now be added.
--we now check against the degreeList to see if this addition can occur.
--if not, then this multiset is not included in the sum for that value of j.
	    if (degreeList_(columnCount-1) > listOfPowers_(columnCount-1))
	    then
             print(columnCount,
		 listOfPowers,
		 coefficientMatrix_(0,columnCount-1),
	     (1/(deg^(sum listOfPowers+1))),
	     multinomial(listOfPowers)*(listOfPowers_(columnCount-1)+1),
	     varsPowers(listOfPowers,XGens),
	     specialPartial(fy,listOfPowers,YGens,columnCount)); 
	 
    	    coefficientMatrix_(0,columnCount-1) = 
	    coefficientMatrix_(0,columnCount-1)
	    + (1/(deg^(sum listOfPowers+1)))
	    * multinomial(listOfPowers)*(listOfPowers_(columnCount-1)+1)
	    * varsPowers(listOfPowers,XGens)
	    * specialPartial(fy,listOfPowers,YGens,columnCount);
	 );
     );
matrix coefficientMatrix
)
        
end
restart
load "cleverFactor.m2"
listBuilder({1,1,1},3)
R = QQ[x_1,x_2,x_3]
f = x_1+x_2+x_3
M = cleverFactor(f)
A = matrix{{x_1-y_1},{x_2-y_2},{x_3-y_3}}
first(flatten(entries (M*A)))

restart
load "cleverFactor.m2"
listBuilder({0,0,2},2)
R = QQ[x_1,x_2,x_3]
f = x_3^2
M = cleverFactor(f)
A = matrix{{x_1-y_1},{x_2-y_2},{x_3-y_3}}
first(flatten(entries (M*A)))

restart
load "cleverFactor.m2"
R = QQ[x]
M = cleverFactor(x)
y
y

restart
load "cleverFactor.m2"
R = QQ[x_1,x_2]
f = x_1^2+x_1*x_2
listBuilder({2,1},2)
M = cleverFactor(f)
A = matrix{{x_1-y_1},{x_2-y_2}}
first(flatten(entries (M*A)))
