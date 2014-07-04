module Search{  

  method FindMax(a: array<int>) returns (currentMaxIndex: int)
    requires a != null && a.Length >= 1;
    ensures 0 <= currentMaxIndex < a.Length;
    ensures forall k :: 0 <= k < a.Length ==> a[currentMaxIndex] >= a[k];
  {
    var index := 1;
    currentMaxIndex := 0;
    
    while(index < a.Length)
      decreases a.Length - index;
      invariant 0 <= currentMaxIndex < index <= a.Length;
      invariant forall k :: 0 <= k < index <= a.Length ==> a[currentMaxIndex] >= a[k];
    {
        if(a[index] > a[currentMaxIndex])
        {
          currentMaxIndex := index;
        }
        index := index + 1;
    }
  }

  method FindMin(a: array<int>) returns (currentMinIndex: int)
    requires a != null && a.Length >= 1;
    ensures 0 <= currentMinIndex < a.Length;
    ensures forall k :: 0 <= k < a.Length ==> a[currentMinIndex] <= a[k];
  {
    var index := 1;
    currentMinIndex := 0;
    
    while(index < a.Length)
      decreases a.Length - index;
      invariant 0 <= currentMinIndex < index <= a.Length;
      invariant forall k :: 0 <= k < index <= a.Length ==> a[currentMinIndex] <= a[k];
    {
        if(a[index] < a[currentMinIndex])
        {
          currentMinIndex := index;
        }
        index := index + 1;
    }
  }

  predicate sorted(a: array<int>, low: int, high : int)
    requires a != null && 0 <= low <= high < a.Length;
    reads a;
  {
    forall j, k :: low <= j < k <= high ==> a[j] <= a[k]
  }
  
}