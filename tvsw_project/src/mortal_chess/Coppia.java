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
	
}
