--Returns the digits in nn which are nonzero in binary 
--for example, 5 in binary is 101, so this would return {0,2}
--the second term tells me where to start the count, so passing
--5,0 gives {0,2} but 5,1 is sent to {1,3}.  i=!=0 should be
--used only for recursive purposes
getNonzeroBinaryDigits = (nn, i) -> (
--    error "breakme";
    halfsies := nn//2;
    val1 := nn%2;
    val2 := false; 
    if (halfsies > 0) then val2 = (getNonzeroBinaryDigits(nn//2,i+1));
    if ( (val1 != 0) and (not (val2 === false))) then (
	 flatten {i, val2}
    )
    else if (val1 != 0) then (
	 {i}
    )
    else if ( not (val2 === false)) then (
	 flatten {val2}
    )
    else(
	 false
    )
)

--Returns the entries of myList specified by entryList
--For example, ( {1,2,3}, {0,2}) is sent to {1,3}
getSublistOfList = (myList, entryList) -> (
     --error "help";
     apply( #entryList, i->myList#(entryList#i) )
)

--Returns the power set of a given list, leaving out the emptyset.  
--E.g. {2,3,4} becomes { (2),(3),(4),(2,3),(2,4),(3,4),(2,3,4) }
--as applied to cleverFactor, nontrivialPowerSet will help index all possible
--candidates for the set A over which the sum is indexed.
nontrivialPowerSet = (myList) ->(
     apply(2^(#myList)-1, i-> getSublistOfList(myList, getNonzeroBinaryDigits(i+1,0) ) )
)

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

sumSequence = (mySequence) -> (
    sum(toList(mySequence))
)

multinomial = (mySeqnence) -> (
     (factorial(sumSequence(mySeqnence)))/(sumSequence(mySeqnence / factorial))
)

varsPowers = (mySequence,myVars) -> (
    holder = 1;
    for i from 0 to (#mySequence -1) do (
	holder = holder*(myVars__i)^(mySequence_i);
    );
    holder	
)            

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
--creating the new variables for the ring representing the enveloping algebra    
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
    deg := degree f;
--the placeholder for the coefficients of each (x_j-y_j)    
    coefficientMatrix = mutableMatrix(myNewRing, 1, numVars);
    degreeSequence = buildDegreeSequence(f);
--create and populate an sequence to track the exponents	
    sequenceOfPowers = ();
    for i from 1 to numVars do (
	sequenceOfPowers = append(sequenceOfPowers, 0);
    );
    indexCounter = 0;
--a large loop; columnCount tracking will occur within 
--the selection of each sequenceOfPowers, as there is
--a great deal of repitition.
    finishd = false;
    while finished == false do (
	prepped = false;
	while prepped == false do (
	    if (sequenceOfPowers_indexCounter < degreeSequence_indexCounter) then
	    sequenceOfPowers_indexCounter = sequenceOfPowers_indexCounter+1
	    else sequenceOfPowers_indexCounter = 0
	    


--columnCount tracks the index of x_j-y_j    
    for columnCount from 1 to numVars do (
	if degreeSequence_(columnCount-1) > sequenceOfPowers_(columnCount-1) 
	then coefficientMatrix_(0,columnCount-1) = 
	coefficientMatrix_(0,columnCount-1)
	+ (1/deg^(sumSequence(sequenceOfPowers)+1))
	* multinomial(sequenceOfPowers)
	* varsPowers(sequenceOfPowers,YGens)
	* specialPartial(f,sequenceOfPowers) ;
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
R = QQ[x_1,x_2]
f = x_1^2+x_1*x_2
