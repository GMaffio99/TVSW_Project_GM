package mortal_chess;

public abstract class Pedina {
	
	private /*@ spec_public @*/ char giocatore;
	private /*@ spec_public @*/Coppia<Integer, Character> cella;
	
	/*@ requires g == 'X' || g == 'O';
	  @ requires r >= 1 && r <= 8;
	  @ requires c >= 'A' && c <= 'H';
	  @ ensures this.giocatore == g;
	  @ ensures this.cella.getPrimo() == r;
	  @ ensures this.cella.getSecondo() == c;
	  @*/
	public Pedina(char g, int r, char c) {
		giocatore = g;
		cella = new Coppia(r, c); // TODO sistemare il warning e farlo notare
	}
	
	//@ ensures \result == this.giocatore;
	//@ pure
	public char getGiocatore() {
		return giocatore;
	}
	
	//@ ensures \result == this.cella.getPrimo();
	//@ pure
	public int getRiga() {
		return cella.getPrimo();
	}
	
	//@ ensures \result == this.cella.getSecondo();
	//@ pure
	public char getColonna() {
		return cella.getSecondo();
	}
	
	//@ ensures this.cella.getPrimo() == r;
	public void setRiga(int r) {
		cella.setPrimo(r);
	}
	
	//@ ensures this.cella.getSecondo() == c;
	public void setColonna(char c) {
		cella.setSecondo(c);
	}
	
	//@ pure
	public abstract boolean isAttaccante();
	//@ pure
	public abstract boolean isDifensore();
	
	//@ ensures \result == true <==> (this.isAttaccante() == true && isDifensore() == true);
	//@ pure
	public boolean isAttaccanteDifensore() {
		return isAttaccante() && isDifensore();
	}
	
	//@ ensures this.cella.getPrimo() == r && this.cella.getSecondo() == c;
	public void muovi(int r, char c) {
		setRiga(r);
		setColonna(c);
	}
	
	public abstract Pedina unisci(Pedina p);
	
	public abstract boolean vieneAttaccata(int p);
	
	
	@Override
	public String toString() {
		return "" + getColonna() + getRiga();
	}
	
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (!(obj instanceof Pedina))
			return false;
		Pedina p = (Pedina) obj;
		return this.getGiocatore() == p.getGiocatore() &&
				this.getRiga() == p.getRiga() &&
				this.getColonna() == p.getColonna();
	}
	
}
