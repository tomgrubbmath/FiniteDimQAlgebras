FDQA = new Type of VisibleList
FDQAElement = new Type of VisibleList

fDQA = method()

fDQA VisibleList := FDQA => H -> new FDQA from H


hashFDQA = method()

hashFDQA FDQA := MutableHashTable => A -> (
    H := new MutableHashTable;
    dimension := #A;
    for k from 0 to dimension-1 do(
	Ak := A_(k);
	--print Ak;
	for j from 0 to dimension-1 do(
	    --print j;
	    for i from 0 to dimension-1 do(
		s:= toString(i+1)|toString(j+1)|toString(k+1);
		--print s;
		H#s = Ak_j_i)));
    return H)

fDQAElement = method()

fDQAElement VisibleList := FDQAElement => H -> new FDQAElement from H

FDQAElement + FDQAElement := (a,b) -> (
    assert(#a == #b);
    l := for i from 2 to #a list a_(i-1)+b_(i-1);
    l = prepend(a_0,l);
    return fDQAElement l)

FDQAElement - FDQAElement := (a,b) -> a+(-1)*b;

ZZ * FDQAElement := (a,b) -> (
    l:= for i from 2 to #b list a*b_(i-1);
    l = prepend(b_0,l);
    return fDQAElement l)


QQ * FDQAElement := (a,b) -> (
    l:= for i from 2 to #b list a*b_(i-1);
    l = prepend(b_0,l);
    return fDQAElement l)

FDQAElement*QQ := (a,b) -> b*a

FDQAElement*FDQAElement := (a,b) ->(
    CommonAlgebra := hashFDQA(a_0);
    e = a - a;
    --print(e);
    for i from 1 to #a-1 do(	
	for j from 1 to #a-1 do(
	    l := {};
	    for k from 1 to (#a-1) do(
		--print (toString(i)|toString(j)|toString(k));
		l = append(l,a_i*b_j*CommonAlgebra#(toString(i)|toString(j)|toString(k))));
	    lFDQA := fDQAElement prepend(a_0,l);
	    e = e+lFDQA));
    return e)


	    
M = matrix{{1,0},{0,2}}
N = matrix{{0,1},{1,0}}	    
A = fDQA {M,N}
l = fDQAElement {A,1,1}		
(3/1)*l		
l+l
l-l
l*l
l
j = fDQAElement {A,3,1}
k = fDQAElement {A,1,-1}
j*k
k*j
