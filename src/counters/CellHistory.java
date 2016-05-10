package counters;

public class CellHistory {

	private  final /*@ spec_public non_null @*/ IntegerLista list;
	

	
	
	public CellHistory(){
		list = new IntegerLista();
	}
	

	/*@ requires list != null && list.getSize() <=  0;
	   		ensures \result == 0;
	   		also
	   		requires list != null && list.getSize() > 0;
	 		ensures \result == list.getItem(list.getSize()-1);
	 */
	public /*@ pure non_null@*/ int read(){
		
		if(list != null && list.getSize() <= 0){
			return 0;
		}else{
			if(list != null )
				return  list.getItem(list.getSize()-1);
			else return 0;
		}
	}
	
	
	/*@ ensures \result == (I >=0);
	 */
	public /*@ pure non_null @*/ boolean cadd(Integer I){
		return I>= 0;
	}
	
	
	
	/*@ requires cadd(I) ;
	  @ ensures 
	  @ read() == I;
	  @ also
	  @ requires !cadd(I);
	  @ assignable \nothing;
	 */
	public void add(/*@ non_null @*/ Integer I){
			if(list != null && list.getSize() >= 0 && cadd(I)){
					if(I != null ){
							list.add(I);
					}
			}
	}//end of add
	
	
	
}
