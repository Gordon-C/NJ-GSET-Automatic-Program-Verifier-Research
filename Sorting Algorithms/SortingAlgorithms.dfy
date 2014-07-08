import Search

	method BubbleSort(a: array<int>)
	  requires a != null && a.Length > 1;
	  modifies a;
	  ensures sorted(a, 0, a.Length); //sortedUntil is exclusive
	{ 
	  var sortedUntil := 0;
	  var i := a.Length - 1;
	  
	  while(sortedUntil < a.Length)
	    invariant 0 <= sortedUntil <= a.Length;
	    invariant forall j, k :: 0 <= j < sortedUntil <= k < a.Length ==> a[j] <= a[k]; //all sorted elements are less than or = to unsorted elements
	    invariant sorted(a, 0, sortedUntil);
	  {
	    i := a.Length - 1;
	    while(i > sortedUntil) 
	      invariant sortedUntil <= i < a.Length;
	      invariant forall j, k :: 0 <= j < sortedUntil <= k < a.Length ==> a[j] <= a[k]; //all sorted elements are less than or = to unsorted elements
	      invariant forall j :: i <= j < a.Length ==> a[i] <= a[j]; //current element being inspected is less than elements after it (array is sorted every time you finish inner loop)
	      /*
	        Line 20 states array[0..sortedUntil) is sorted every time the inner loop is finished, meaning the sorted portion will grow and still be 
	        sorted at each iteration of the loop. Since every element in the unsorted portion is greater than every element in
	        sorted portion (established by line 19), then adding an element to the sorted portion from the unsorted portion will maintain
	        "sortedness." Furthermore, by line 19, the shrunken unsorted portion contains only elements greater than the increased
	        sorted portion. Repeat this logic until the entire array is sorted.
	      */
	      //invariant forall j :: 0 <= j < sortedUntil ==> a[i] >= a[j]; //current element being inspected is greater than all elements in sorted portion
	      invariant sorted(a, 0, sortedUntil);
	    {
	      if(a[i] <= a[i - 1])
	      {
	        a[i - 1], a[i] := a[i], a[i-1]; //swap
	      }
	      i := i - 1; 
	    }
	    sortedUntil := sortedUntil + 1;
	  }
	  //sorted(a, 0, a.Length) -> sortedUntil + 1 == a.Length (true)
	}

	//ensures subarray of indices [low, high) is sorted
	predicate sorted(a: array<int>, low: int, high: int)
	  requires a != null;
	  requires 0 <= low <= high <= a.Length;
	  reads a;
	{
	  forall j, k :: low <= j < k < high ==> a[j] <= a[k]
	}

}