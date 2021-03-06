package counters;

public class IntegerLista {

	private /*@ spec_public non_null@*/  Integer[] items ;
	/*@  public invariant items != null  && 0 <= items.length 
	            && (\typeof(items) == \type(Integer[]) ) 
	 			&&	\elemtype(\type(Integer[])) == \type(Integer);
	 */
	
	public final /*@ non_null @*/ Integer err ;
	
	public IntegerLista(){
		items = new Integer[0];
		err = new Integer(0);
	}
	
	/*@ modifies \nothing;  
    @   requires items != null && id < items.length && id >= 0 
    		&& items[id] != null && items.length > 0;
 	@ ensures \result == items[id] && \result != null;
 	@ also
 	@ requires  items != null && ( id >= items.length || id < 0 
 	|| items[id] == null || items.length <= 0);
 	@ ensures \result == err && \result != null;
 */
	public /*@ pure non_null@*/ Integer getItem(int id){
		if(items.length <= 0){
			return err;
		}else{
			if(items != null && id < items.length && id >=0 
					&& items[id] != null && items.length > 0)
				return items[id];
			else return err;
		}
	}//getItem
	
	
	/*@ ensures \result == items.length;
	    @ also
	    @ ensures \result >= 0; 
	 */
	public /*@ pure @*/ int getSize(){return items.length;}
	
	
	
	/*@ requires items != null  && items.length  >=0 && size > items.length && size > 0;
		@ ensures items != null ;
		@ also
		@ requires items != null  && items.length  >=0 && size > items.length && size > 0;
		@ ensures items.length == size;
		@ also
		@ requires items != null  && items.length  >=0 && size > items.length && size > 0;
		@ ensures (\forall int j; j >=0 && j < \old(items.length); items[j] == \old(items[j]) );
	 */
	public  void resizeArray( int size){

		if(items != null  && items.length  >=0 && size > items.length && size > 0){
			Integer[] temp = new Integer[size];
			/*@ loop_invariant items!= null && temp != null && (items.length < temp.length) ==> 
		    (\forall int j; (j >= 0 && j < i  )
		     ==> ( (j < items.length) ==> temp[j] == items[j] )
		      && (!(j < items.length) ==>  temp[j] == null) ) ;
		   decreasing temp.length-i;
			  */
			for(int i = 0; i < temp.length; i++){
				if(i < items.length && i >=0 ) temp[i] = items[i];
				 else{ 
					 if(i >=0)  temp[i] = null;
				 }
			 }//end of for loop
			items =temp;
		}
	}//end of reseizeArray

	
	/*@ requires it != null &&  pos >= 0 && pos < items.length;
			ensures getItem(pos) == it;
			assignable items[pos]; 
	 */
	public void assign(/*@ non_null@*/ Integer it, int pos){
		if(it != null && pos >=0 && pos < items.length){
			items[pos] = it;
		}
	}
	
	

	/*@  requires   pos >= 0 && pos >= getSize() && getSize() >0 ;
	 		 ensures items != null && getSize() == pos+1;
	 		 also
	 		 requires   pos >= 0 && pos >= getSize() && getSize() >0 ;
	 		 ensures getItem(pos) == it;
	 		 also
	 		 requires   pos >= 0 && pos < getSize() && getSize() >0 ;
	 		 ensures getItem(pos) == it;
	 		 also
	 		 requires   pos >= 0 && pos < getSize() && getSize() >0 ;
	 		 ensures \old(getSize()) == getSize();
	 */
	public void setItem(int pos, /*@ non_null @*/ Integer it){
		if( items != null  && items.length  >0 && pos >= items.length && pos > 0){
			resizeArray(pos+1);
			if(it != null && pos >= 0 && pos < items.length){ 
				assign(it,pos);
			}
		}
		
		if( items != null  && items.length  >0 && pos < items.length && pos >= 0){
			if(it != null && pos >= 0 && pos < items.length){ 
				assign(it,pos);
			}
		}
	}//end of setItem
	
	
	
	
	
	
	/*@ ensures getSize() > 0;
	    @ also
	    @ requires getSize() > 0;
	  	@ ensures getItem(getSize()-1) == obj;
	  	@ also 
	  	@ requires getSize() == 0;
	  	@ ensures getItem(getSize()-1) == obj;
	 */
	public void add(/*@ non_null @*/ Integer obj){
		if(getSize() >0){
			setItem(getSize(),obj) ;
		}else{
			if(getSize() == 0){
				resizeArray(1);
				items[0] = obj;
			}
		}
	}
	
	
}//end of lista
