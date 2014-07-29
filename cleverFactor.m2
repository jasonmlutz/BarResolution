--performs partial derivatives of the given polynomial by
--the variables in the given list
specialPartial = (myPolynomial,powersList, variablesList,bonus) -> (
    if not (#powersList == #variablesList) then error "expected two lists of same size";
    myRing = ring myPolynomial;
    if not (isSubset(variablesList, gens myRing)) then error "expected argument 3 to be a subset of the generators of the ring";
{*    myRing = ring myPolynomial;
    numVars := length gens myRing;
    myVars = {};
    for k from ((numVars)/2) to (numVars-1) do (
	myVars = append(myVars, (gens myRing)_k);
	);    
    *}
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

--this is broken. I don't know why.
{*
sumSequence = (mySequence) -> (
    myList = (toList mySequence);
    sum(myList)
) *}

multinomial = (myList) -> (
{*    myList = (toList mySequence);
    upperPrep = sum myList;
    upper = factorial upperPrep;
    lowerPrep = myList / factorial;
    lower = sum(lowerPrep);
    upper / lower *}
     (factorial(sum myList))/(product(myList / factorial))
)

varsPowers = (myList,myVars) -> (
    holder = 1;
    for i from 0 to (#myList -1) do (
	holder = holder*(myVars_i)^(myList_i);
    );
    holder	
)            

--for debugging which loop is broken
--end

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
--create and populate a list to track the exponents	&
--create and populate a list to track whether overflow
--can occur during the counting procedure; constructed to be
--0 in the case that a variable does not appear in the input
--polynomial f
    listOfPowers = {};
--not needed; check listOfPowers directly	    
--    overflowTracker = ();
    for i from 1 to numVars do (
	listOfPowers = append(listOfPowers, 0);
--	overflowTracker = append(overflowTracker,min(1,degreeList_(i-1))); 
    );
--a large loop; columnCount tracking will occur within 
--the selection of each listOfPowers, as there is
--a great deal of repitition.

--debug zone
--ans = read "debug 1? y or n "; if ans == "y" then print listOfPowers;

    finished = false;
    while finished == false do (
--we have a reasonable listOfPowers 
--so perform the changes to coefficientMatrix    
--columnCount tracks the index of x_j-y_j    
        for columnCount from 1 to numVars do (
--for each j, the general algorithm sums over these multisets that contain j.
--to make the above construction apply independently of j, the multisets above
--were allowed to have, at most, deg-1 terms, so that one more y_j can now be added.
--we now check against the degreeList to see if this addition can occur.
--if not, then this multiset is not included in the sum for that value of j.

--degug zone
--ans = read "pre-coefficientMatrix adjust debug? y or n: "; if ans == "y" then print (columnCount, degreeList,listOfPowers);
	    if (degreeList_(columnCount-1) > listOfPowers_(columnCount-1))
--debug zone
	    then
--	    ans = read "coefficientMatrix verbose debug? y or n: "; 
--    if ans == "y" then 
             print(columnCount,
		 listOfPowers,
		 coefficientMatrix_(0,columnCount-1),
	     (1/(deg^(sum listOfPowers+1))),
	     multinomial(listOfPowers),
	     varsPowers(listOfPowers,YGens),
	     specialPartial(fy,listOfPowers,YGens,columnCount));
    coefficientMatrix_(0,columnCount-1) = 
	    coefficientMatrix_(0,columnCount-1)
	    + (1/(deg^(sum listOfPowers+1)))
	    * multinomial(listOfPowers)
	    * varsPowers(listOfPowers,YGens)
	    * specialPartial(fy,listOfPowers,YGens,columnCount);
		
--(re)set the need for overflow	    
	activateOverflow = false;
--check if current total degree forces overflow
--the deg-1 is since we're secretly going to add one factor
--of y_j as j varies, then ignore it for parts of the computation,
--so there needs to be room to make this later addition

--debug zone
--ans = read "debug 2? y or n "; if ans == "y" then print (listOfPowers,activateOverflow,finished,(sum(toList listOfPowers) >=  (deg-1)));

	if ((sum listOfPowers) >=  (deg-1))
--queue the overflow; staring with the 2nd entry	    
	then (
	    activateOverflow = true; 
	    overflowColumn = 2;
	)
	else (
--check if an addition attempt in the "ones" place forces overflow
	if (listOfPowers_0 >= degreeList_0)
--queue the overflow; staring with the 1st entry	    	    
	then (
	    activateOverflow = true;
	    overflowColumn = 1;
	)
	);
    
--debug zone
--ans = read "debug 3? y or n "; if ans == "y" then print (listOfPowers,activateOverflow,finished);

    	
--check if there is space to perform the addition in the "ones" place
	if activateOverflow = false
--there is space. perform the addition. prepped for coefficientMatrix
	then (listOfPowers_0 = (listOfPowers_0)+1)
	else (
--activate overflow protocol:
--begin search for the next column that has space for addition,
--and that there is a column left to consider		
	overflowLocated = false;
--debug zone	
--ans = read "debug 4? y or n "; if ans == "y" then print (listOfPowers,overflowColumn, overflowLocated, overflowColumn <= (deg-1));	
	while ((overflowLocated == false) and (overflowColumn <= (deg))) do (
--check if the current column allows for addition		
--debug zone
--ans = read "debug 5? y or n "; if ans4 == "y" then print (listOfPowers,overflowColumn);
	    if (listOfPowers_overflowColumn < degreeList_overflowColumn)
	    then (overflowLocated = true)
--if not, move to the next.		
	    else (overflowColumn = overflowColumn+1)
	);
--asses the reason that the preceeding search for the overflowColumn was terminated,
--i.e., have we reached the end?	
	if (overflowColumn <= (deg))
	then (
--increase by 1 in the overflow column	    
    	tempList = {};
	for i from 0 to ((#listOfPowers)-1) do (
	    if i == overflowColumn then (
		tempList = append(tempList, (listOfPowers_overflowColumn)+1))
	    else tempList = append(tempList, listOfPowers_overflowColumn)
	    );
	listOfPowers = tempList;
--reset all lower columns to 0	    
    	tempList = {};
	for i from 0 to (overflowColumn - 1) do (
    	    tempList = append(tempList,0)
	    );
	for i from overflowColumn to ((#listOfPowers) - 1) do (
	    tempList = append(tempList, listOfPowers_i)
	    );
	)
--there isn't enough space to overflow, so we're done.	
	else (finished = true );
--debug zone
--ans = read "debug 6? y or n "; if ans == "y" then print (listOfPowers,overflowColumn,finished);	
	);
   );
    );
matrix coefficientMatrix
)
        
{* --this original algorithm won't work; need to account for possible
   --repotition of the variables of differentiation. Consider
   --use of lists rather than sets of variables.
--columnCount tracks the index of x_j-y_j    
    for columnCount from 1 to numVars do (
	varsIndices = 1..numVars; --a list
    	varsIndices = toList indexedVars; --now a list
    	indicesSubset = nontrivialPowerSet(varsIndices); 
	for subsetCounter from 1 to 2^(numVars-1) do (
	    varsSubset = indicesSubset_subsetCounter;
	    if isSubset(set{columnCount},varsSubset) then
	    for j in varsSubset do (
		varFactor = 1;
		for a in varsSubset do (
		    if a=!=columnCount then varFactor = varFactor*XGens_(a-1)
		);
    	    	coefficientMatrix_(0,columnCount) = (1/d^(# varsSubset))*varFactor*specialPartial(fy,yVarsSubset);
		);
	);
    ); *} --end of original




end
restart
load "cleverFactor.m2"
R = QQ[x_1,x_2,x_3]
f = x_1+x_2+x_3
M = cleverFactor(f)
A = matrix{{x_1-y_1},{x_2-y_2},{x_3-y_3}}
first(flatten(entries (M*A)))

restart
load "cleverFactor.m2"
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

R = QQ[x_1,x_2]
f = x_1^2+x_1*x_2
