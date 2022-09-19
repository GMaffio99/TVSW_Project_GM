package mortal_chess;

public abstract class Pedina {
	
	private char giocatore;
	private Coppia<Integer, Character> cella;
	
	public Pedina(char g, int r, char c) {
		giocatore = g;
		cella = new Coppia(r, c); // TODO sistemare il warning e farlo notare
	}
	
	
	public char getGiocatore() {
		return giocatore;
	}
	
	public int getRiga() {
		return cella.getPrimo();
	}
	
	public char getColonna() {
		return cella.getSecondo();
	}
	
	public void setRiga(int r) {
		cella.setPrimo(r);
	}
	
	public void setColonna(char c) {
		cella.setSecondo(c);
	}
	
	
	public abstract boolean isAttaccante();
	public abstract boolean isDifensore();
	
	public boolean isAttaccanteDifensore() {
		return isAttaccante() && isDifensore();
	}
	
	
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
