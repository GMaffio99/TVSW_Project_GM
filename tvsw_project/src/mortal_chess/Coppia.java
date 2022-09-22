package mortal_chess;

public class Coppia<P, S> {
	
	private /*@ spec_public @*/ P primo;
	private /*@ spec_public @*/ S secondo;
	
	public Coppia(P p, S s) {
		primo = p;
		secondo = s;
	}
	
	//@ ensures \result.equals(this.primo);
	//@ pure
	public P getPrimo() {
		return primo;
	}
	
	//@ ensures \result.equals(this.secondo);
	//@ pure
	public S getSecondo() {
		return secondo;
	}
	
	//@ ensures this.primo.equals(p);
	public void setPrimo(P p) {
		primo = p;
	}
	
	//@ ensures this.secondo.equals(s);
	public void setSecondo(S s) {
		secondo = s;
	}
	
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (!(obj instanceof Coppia<?,?>))
			return false;
		Coppia<?,?> c = (Coppia<?,?>) obj;
		return this.getPrimo().equals(c.getPrimo()) && this.getSecondo().equals(c.getSecondo());
	}
	
}
