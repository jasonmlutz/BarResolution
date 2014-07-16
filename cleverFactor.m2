--performs partial derivatives of the given polynomial by
--the variables in the given sequence
specialPartial = (myPolynomial,varsSequence) -> (
    myRing = ring myPolynomial;
    if not isSubset(toList(varsSequence),gens myRing) 
    then error "expected argument 2 to be a sequence of generators of the ring";
    diffed = myPolynomial;
    for i from 1 to #varsSequence do (    
	diffed = diff(varsSequence_(i-1),diffed) );
    diffed
)--works!

--build a sequence consisting of the highest power
--of each variable appearing; for use in optimizing the
--number of sequences added to the bag of multisets
buildDegreeSequence = (myPolynomial) -> (
    degreeSequence = ();
    myRing = ring myPolynomial;
    for i from 1 to #gens(myRing) do (
        degreeSequence = append(degreeSequence,degree((gens R)_(i-1),myPolynomial));
    );
    degreeSequence
)--works!        

--build a collection of sequences composed of integers
--1..degree(myPoly)-1, under the condition that an integer
--j must appear no more than degree(y_j,f) times,
--with the exception that the distinguished index i has a bound
--1 less.
--
--This is being abandoned; there is no real need to be able to construct
--such a sequence outside of the cleverFactor method as it will be
--a huge use of memory. Instead, integrate the style of loops into
--clever factor and the long list of sequences will not need to be stored.
multisetSequence = (polyDegree, degreeBounds, distinguishedIndex) -> (
--storage for sequences, ordering allows for duplicates
    bag = ();
--storage for information about repititions in each element of the bag
    bagCount = ();    
--add the empty sequence as an element in bag, bagCount
    bag = append(bag,());    
    bagCount = append(bagCount,0);        
--build the starting structure of one sequence for each allowable value
--of the distinguished index
    for i from 1 to degreeBounds_(distinguishedIndex-1) do (
	nextBagMember = ();
--structure for counting how many copies will be added	
	nextBagCountMember = ();
	copyCount = 0;
--fill this bag with the right number of copies of the distinguished index	    
	for j from 1 to i do (
	    nextBagMember = append(nextBagMember,distinguishedIndex);
	    );
	bag = append(bag, nextBagMember);
--	print bag; --for debugging
	);
    bag
)

factorial = i -> (
    i!
)    

--this is broken. I don't know why.
{*
sumSequence = (mySequence) -> (
    myList = (toList mySequence);
    sum(myList)
) *}

multinomial = (mySeqnence) -> (
     (factorial(sum(toList mySeqnence)))/(sum(toList mySeqnence / factorial))
)

varsPowers = (mySequence,myVars) -> (
    holder = 1;
    for i from 0 to (#mySequence -1) do (
	holder = holder*(myVars_i)^(mySequence_i);
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
--the sequence consisting of the (highest) degrees of each variable
    degreeSequence = buildDegreeSequence(f);
--create and populate a sequence to track the exponents	&
--create and populate a sequence to track whether overflow
--can occur during the counting procedure; constructed to be
--0 in the case that a variable does not appear in the input
--polynomial f
    sequenceOfPowers = ();
--not needed; check sequenceOfPowers directly	    
--    overflowTracker = ();
    for i from 1 to numVars do (
	sequenceOfPowers = append(sequenceOfPowers, 0);
--	overflowTracker = append(overflowTracker,min(1,degreeSequence_(i-1))); 
    );
--a large loop; columnCount tracking will occur within 
--the selection of each sequenceOfPowers, as there is
--a great deal of repitition.
    finished = false;
    while finished == false do (
--(re)set the need for overflow	    
	activateOverflow = false;
--check if current total degree forces overflow
--the deg-1 is since we're secretly going to add one factor
--of y_j as j varies, then ignore it for parts of the computation,
--so there needs to be room to make this later addition
	if (sum(toList sequenceOfPowers) >=  (deg-1)) 
--queue the overflow; staring with the 2nd entry	    
	then (
	    activateOverflow = true; 
	    overflowColumn = 2;
	)
	else (
--check if an addition attempt in the "ones" place forces overflow
	if (sequenceOfPowers_0 >= degreeSequence_0)
--queue the overflow; staring with the 1st entry	    	    
	then (
	    activateOverflow = true;
	    overflowColumn = 1;
	)
	);	
--check if there is space to perform the addition in the "ones" place
	if activateOverflow = false
--there is space. perform the addition. prepped for coefficientMatrix
	then (sequenceOfPowers_0 = (sequenceOfPowers_0)+1)
	else (
--activate overflow protocol:
--begin search for the next column that has space for addition,
--and that there is a column left to consider		
	overflowLocated = false;
	while ((overflowLocated == false) and (overflowColumn <= (deg-1))) do (
--check if the current column allows for addition		
	    if (sequenceOfPowers_overflowColumn < degreeSequence_overflowColumn)
	    then (overflowLocated = true)
--if not, move to the next.		
	    else (overflowColumn = overflowColumn+1)
	);
--asses the reason that the preceeding search for the overflowColumn was terminated,
--i.e., have we reached the end?	
	if (overflowColumn <= (deg-1))
	then (
--increase by 1 in the overflow column	    
	sequenceOfPowers_overflowColumn = sequenceOfPowers_overflowColumn + 1;
--reset all lower columns to 0	    
	for i from 0 to (overflowColumn - 1) do (
	    sequenceOfPowers_i = 0
	    );
	)
--there isn't enough space to overflow, so we're done.	
	else (finished = true )
	);
--otherwise, we've made some reasonable adjustment to the sequenceOfPowers,
--so perform the changes to coefficientMatrix    
        if finished = false 
        then (
--columnCount tracks the index of x_j-y_j    
        for columnCount from 1 to numVars do (
--for each j, the general algorithm sums over these multisets that contain j.
--to make the above construction apply independently of j, the multisets above
--were allowed to have, at most, deg-1 terms, so that one more y_j can now be added.
--we now check against the degreeSequence to see if this addition can occur.
--if not, then this multiset is not included in the sum for that value of j.
	    if (degreeSequence_(columnCount-1) > sequenceOfPowers_(columnCount-1))
	    then coefficientMatrix_(0,columnCount-1) = 
	    coefficientMatrix_(0,columnCount-1)
	    + (1/deg^(sum(toList sequenceOfPowers)+1))
	    * multinomial(sequenceOfPowers)
	    * varsPowers(sequenceOfPowers,YGens)
	    * specialPartial(f,sequenceOfPowers);
	);
        );
    );
coefficientMatrix
)
        
{* --this original algorithm won't work; need to account for possible
   --repotition of the variables of differentiation. Consider
   --use of sequences rather than sets of variables.
--columnCount tracks the index of x_j-y_j    
    for columnCount from 1 to numVars do (
	varsIndices = 1..numVars; --a sequence
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
R = QQ[x]
cleverFactor(x)
c
R = QQ[x_1,x_2]
f = x_1^2+x_1*x_2
