package counters;

public class Counter{

	private /*@ spec_public non_null @*/ int cell;
	
	/*@ ensures read() == 0;
	 */
	public Counter(){
		cell = 0;
	}
	

	/*@ ensures \result == cell;
	 */
	public /*@ pure non_null@*/ int read(){return this.cell;}
	
	/*@ ensures \result == (I >=0);
	 */
	public /*@ pure non_null @*/ boolean cadd(int I){
		return I>= 0;
	}

	/*@ requires cadd(I);
	  @ ensures 
	  @ read() ==  I;
	  @ also
	  @ requires !cadd(I);
	  @ assignable \nothing; 
	 */
	public void add(int I){
		if(cadd(I)){
			cell =  I;
		}
	}
	

}