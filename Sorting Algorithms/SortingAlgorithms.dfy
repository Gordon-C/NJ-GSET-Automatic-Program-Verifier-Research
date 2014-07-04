import Search

method BubbleSort(a: array<int>) returns (sortedArr: array<int>)
  requires a != null && a.Length >= 1;
  modifies a;
  ensures sortedArr != null && sortedArr.Length >= 1 && sorted(sortedArr, 0, sortedArr.Length - 1);
{
  sortedArr := a;
  
  var indexToBePlaced: int := 0;
  var counter: int := sortedArr.Length - 1;
  
  while(indexToBePlaced < sortedArr.Length)
    decreases sortedArr.Length - indexToBePlaced;
    invariant 0 <= indexToBePlaced <= sortedArr.Length; 
    invariant 1 <= indexToBePlaced <= sortedArr.Length ==> sorted(sortedArr, 0, indexToBePlaced - 1);
  {
    counter := (sortedArr.Length - 1) - indexToBePlaced;
    
    while(counter > indexToBePlaced)
      decreases counter;
      //invariant 0 <= counter < sortedArr.Length;
      //invariant indexToBePlaced < counter <= sortedArr.Length;
      invariant 1 <= indexToBePlaced <= sortedArr.Length ==> sorted(sortedArr, 0, indexToBePlaced - 1);
    {
      if(sortedArr[counter - 1] > sortedArr[counter])
      {
        sortedArr[counter], sortedArr[counter - 1] := sortedArr[counter - 1], sortedArr[counter];
      }
      //assert indexToBePlaced < counter <= sortedArr.Length;
      counter := counter - 1;
    }
    
    indexToBePlaced := indexToBePlaced + 1;
  }
}