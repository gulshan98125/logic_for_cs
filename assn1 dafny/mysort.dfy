predicate permutation (a:seq<int>, B: seq<int>)
{multiset (a) == multiset (B)}

predicate partOrdered (a:array<int>, lo:int, hi:int)
    requires a != null
    requires 0 <= lo <= hi <= a.Length
    reads a
{
forall i,j:: lo <= i < j < hi ==> a[j] <= a[i]
}

predicate ordered (a:array<int>)
    requires a != null
    reads a
    {
        partOrdered (a, 0, a.Length)
    }
    
method findMaxIndex(a:array<int>,i:int) returns (m:int)
    requires a != null
    requires 0 <= i < a.Length
    ensures i <= m < a.Length
    ensures forall k:: i <= k < a.Length ==> a[k] <= a[m]
{
    var j := i;
    m := i;
    while (j < a.Length)
        invariant i <= j <= a.Length;
        invariant i <= m < a.Length;
        invariant forall k :: i <= k < j ==> a[k] <= a[m];
        {
            if(a[j] > a[m]){m := j;}
            j := j + 1;
        }
}

method selectionSort(a:array<int>)
    requires a != null
    modifies a
    requires a.Length > 0
    ensures ordered(a)
    ensures permutation (a[..], old(a[..]))
{
    var m := 0;
    var i := 0;
    while(i < a.Length)
        invariant 0 <= i <= a.Length;
        invariant partOrdered(a,0,i);
        //invariant i <= m <= a.Length;
        invariant forall k, l :: 0 <= k < i <= l < a.Length ==> a[l] <= a[k];
        invariant permutation (a[..], old(a[..]));
    {
            var t;
            var m := findMaxIndex(a,i);
            assert forall k :: i <= k < a.Length ==> a[k] <= a[m];
            t := a[i];
            a[i] := a[m];
            a[m] := t;
            i := i+1;
    }
}

method Main ()
{
    var A := new int[10];
    A[0], A[1], A[2], A[3], A[4], A[5], A[6], A[7], A[8], A[9] := 4, 8, 8, 3, 5, 10, 9, 9, 4, 7;
    print "A= ", A[..], "\n";
    selectionSort (A);
    print "A= ", A[..], "\n";
}