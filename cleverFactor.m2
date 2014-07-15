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
)--works        

multisetSequence = (polyDegree, degreeBounds) -> (
    bag = {}; --storage for sequences
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
--columnCount tracks the index of x_j-y_j    
    for columnCount from 1 to numVars do (
        
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

    );
coefficientMatrix

)




end
restart
load "cleverFactor.m2"
R = QQ[x_1,x_2]
f = x_1^2+x_1*x_2
