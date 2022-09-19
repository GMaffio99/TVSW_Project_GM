package mortal_chess;

public class Attaccante extends Pedina {

	private int puntiAttacco;
	
	public Attaccante(char g, int r, char c, int p) {
		super(g, r, c);
		puntiAttacco = p;
	}
	
	public Attaccante(char g, int r, char c) {
		this(g, r, c, 1);
	}
	

	public int getPuntiAttacco() {
		return puntiAttacco;
	}
	
	public void setPuntiAttacco(int p) {
		puntiAttacco = p;
	}
	
	
	@Override
	public boolean isAttaccante() {
		return true;
	}

	@Override
	public boolean isDifensore() {
		return false;
	}
	
	
	@Override
	public Pedina unisci(Pedina p) {
		Pedina result;
		if (p.isAttaccanteDifensore()) {
			AttaccanteDifensore t = (AttaccanteDifensore) p;
			result = new AttaccanteDifensore(getGiocatore(), getRiga(), getColonna(), getPuntiAttacco() + t.getPuntiAttacco(), t.getPuntiDifesa());
		}
		else if (p.isDifensore()) {
			Difensore t = (Difensore) p;
			result = new AttaccanteDifensore(getGiocatore(), getRiga(), getColonna(), getPuntiAttacco(), t.getPuntiDifesa());
		}
		else {
			Attaccante t = (Attaccante) p;
			result = new Attaccante(getGiocatore(), getRiga(), getColonna(), getPuntiAttacco() + t.getPuntiAttacco());
		}
		return result;
	}
	
	public boolean attacca() {
		setPuntiAttacco(getPuntiAttacco() - 1);
		return getPuntiAttacco() <= 0;
	}

	@Override
	public boolean vieneAttaccata(int p) {
		return true;
	}

	
	@Override
	public String toString() {
		return super.toString() + " (A) - Punti Attacco: " + getPuntiAttacco();
	}
	
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (!(obj instanceof Attaccante))
			return false;
		Attaccante a = (Attaccante) obj;
		return this.getGiocatore() == a.getGiocatore() &&
				this.getRiga() == a.getRiga() &&
				this.getColonna() == a.getColonna() &&
				this.getPuntiAttacco() == a.getPuntiAttacco();
	}
	
}
