package mortal_chess;

public class Difensore extends Pedina {

	private int puntiDifesa;
	
	public Difensore(char g, int r, char c, int p) {
		super(g, r, c);
		puntiDifesa = p;
	}
	
	public Difensore(char g, int r, char c) {
		this(g, r, c, 1);
	}
	

	public int getPuntiDifesa() {
		return puntiDifesa;
	}
	
	public void setPuntiDifesa(int p) {
		puntiDifesa = p;
	}
	
	
	@Override
	public boolean isAttaccante() {
		return false;
	}

	@Override
	public boolean isDifensore() {
		return true;
	}
	
	
	@Override
	public Pedina unisci(Pedina p) {
		Pedina result;
		if (p.isAttaccanteDifensore()) {
			AttaccanteDifensore t = (AttaccanteDifensore) p;
			result = new AttaccanteDifensore(getGiocatore(), getRiga(), getColonna(), t.getPuntiAttacco(), getPuntiDifesa() + t.getPuntiDifesa());
		}
		else if (p.isDifensore()) {
			Difensore t = (Difensore) p;
			result = new Difensore(getGiocatore(), getRiga(), getColonna(), getPuntiDifesa() + t.getPuntiDifesa());
		}
		else {
			Attaccante t = (Attaccante) p;
			result = new AttaccanteDifensore(getGiocatore(), getRiga(), getColonna(), t.getPuntiAttacco(), getPuntiDifesa());
		}
		return result;
	}
	
	@Override
	public boolean vieneAttaccata(int p) {
		setPuntiDifesa(getPuntiDifesa() - p);
		return getPuntiDifesa() <= 0;
	}

	
	@Override
	public String toString() {
		return super.toString() + " (D) - Punti Difesa: " + getPuntiDifesa();
	}
	
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (!(obj instanceof Difensore))
			return false;
		Difensore d = (Difensore) obj;
		return this.getGiocatore() == d.getGiocatore() &&
				this.getRiga() == d.getRiga() &&
				this.getColonna() == d.getColonna() &&
				this.getPuntiDifesa() == d.getPuntiDifesa();
	}
	
}
