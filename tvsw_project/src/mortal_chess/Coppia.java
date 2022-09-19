package mortal_chess;

public class Coppia<P, S> {
	
	private P primo;
	private S secondo;
	
	public Coppia(P p, S s) {
		primo = p;
		secondo = s;
	}
	
	public P getPrimo() {
		return primo;
	}
	
	public S getSecondo() {
		return secondo;
	}
	
	public void setPrimo(P p) {
		primo = p;
	}
	
	public void setSecondo(S s) {
		secondo = s;
	}
	
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (!(obj instanceof Coppia<?,?>))
			return false;
		return this.equals((Coppia<?,?>) obj);
	}
	
	public boolean equals(Coppia<?, ?> c) {
		return this.getPrimo().equals(c.getPrimo()) && this.getSecondo().equals(c.getSecondo());
	}
	
}
