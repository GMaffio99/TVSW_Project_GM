package mortal_chess;

public class AttaccanteDifensore extends Pedina {

	private int puntiAttacco;
	private int puntiDifesa;
	
	public AttaccanteDifensore(char g, int r, char c, int a, int d) {
		super(g, r, c);
		puntiAttacco = a;
		puntiDifesa = d;
	}
		

	public int getPuntiAttacco() {
		return puntiAttacco;
	}
	
	public void setPuntiAttacco(int p) {
		puntiAttacco = p;
	}
	
	public int getPuntiDifesa() {
		return puntiDifesa;
	}
	
	public void setPuntiDifesa(int p) {
		puntiDifesa = p;
	}
	
	
	@Override
	public boolean isAttaccante() {
		return true;
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
			result = new AttaccanteDifensore(getGiocatore(), getRiga(), getColonna(), getPuntiAttacco() + t.getPuntiAttacco(), getPuntiDifesa() + t.getPuntiDifesa());
		}
		else if (p.isDifensore()) {
			Difensore t = (Difensore) p;
			result = new AttaccanteDifensore(getGiocatore(), getRiga(), getColonna(), getPuntiAttacco(), getPuntiDifesa() + t.getPuntiDifesa());
		}
		else {
			Attaccante t = (Attaccante) p;
			result = new AttaccanteDifensore(getGiocatore(), getRiga(), getColonna(), getPuntiAttacco() + t.getPuntiAttacco(), getPuntiDifesa());
		}
		return result;
	}
	
	public boolean attacca() {
		setPuntiAttacco(getPuntiAttacco() - 1);
		return getPuntiAttacco() <= 0;
	}

	@Override
	public boolean vieneAttaccata(int p) {
		setPuntiDifesa(getPuntiDifesa() - p);
		return getPuntiDifesa() <= 0;
	}

	
	@Override
	public String toString() {
		return super.toString() + " (AD) - Punti Attacco: " + getPuntiAttacco() + " - Punti Difesa: " + getPuntiDifesa();
	}
	
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (!(obj instanceof AttaccanteDifensore))
			return false;
		AttaccanteDifensore ad = (AttaccanteDifensore) obj;
		return this.getGiocatore() == ad.getGiocatore() &&
				this.getRiga() == ad.getRiga() &&
				this.getColonna() == ad.getColonna() &&
				this.getPuntiAttacco() == ad.getPuntiAttacco() &&
				this.getPuntiDifesa() == ad.getPuntiDifesa();
	}
	
}
