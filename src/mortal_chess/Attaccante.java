package mortal_chess;

public class Attaccante extends Pedina {

	private /*@ spec_public; @*/ int puntiAttacco;
	
	/*@ requires g == 'X' || g == 'O';
	  @ requires r >= 1 && r <= 8;
	  @ requires c >= 'A' && c <= 'H';
	  @ requires p >= 1;
	  @ ensures this.giocatore == g;
	  @ ensures this.cella.getPrimo() == r;
	  @ ensures this.cella.getSecondo() == c;
	  @ ensures this.puntiAttacco == p;
	  @*/
	public Attaccante(char g, int r, char c, int p) {
		super(g, r, c);
		puntiAttacco = p;
	}
	
	/*@ requires g == 'X' || g == 'O';
	  @ requires r >= 1 && r <= 8;
	  @ requires c >= 'A' && c <= 'H';
	  @ ensures this.giocatore == g;
	  @ ensures this.cella.getPrimo() == r;
	  @ ensures this.cella.getSecondo() == c;
	  @ ensures this.puntiAttacco == 1;
	  @*/
	public Attaccante(char g, int r, char c) {
		this(g, r, c, 1);
	}
	
	//@ ensures \result == this.puntiAttacco;
	//@ pure
	public int getPuntiAttacco() {
		return puntiAttacco;
	}
	
	//@ requires p >= 1;
	//@ ensures this.puntiAttacco == p;
	public void setPuntiAttacco(int p) {
		puntiAttacco = p;
	}
	
	//@ also ensures \result == true;
	@Override
	public boolean isAttaccante() {
		return true;
	}

	//@ also ensures \result == false;
	@Override
	public boolean isDifensore() {
		return false;
	}
	
	/*@ also
	  @ requires p != null;
	  @ ensures p instanceof AttaccanteDifensore ==> (\result instanceof AttaccanteDifensore &&
	  @ 											((AttaccanteDifensore)\result).getPuntiAttacco() == this.getPuntiAttacco() + ((AttaccanteDifensore)p).getPuntiAttacco() &&
	  @ 											((AttaccanteDifensore)\result).getPuntiDifesa() == ((AttaccanteDifensore)p).getPuntiDifesa());
	  @ ensures p instanceof Difensore ==> (\result instanceof AttaccanteDifensore &&
	  @ 									((AttaccanteDifensore)\result).getPuntiAttacco() == this.getPuntiAttacco() &&
	  @ 									((AttaccanteDifensore)\result).getPuntiDifesa() == ((Difensore)p).getPuntiDifesa());
	  @ ensures p instanceof Attaccante ==> (\result instanceof Attaccante &&
	  @ 									((Attaccante)\result).getPuntiAttacco() == this.getPuntiAttacco() + ((Attaccante)p).getPuntiAttacco());
	  @ ensures (\result).getGiocatore() == this.getGiocatore() && \result.getRiga() == this.getRiga() && \result.getColonna() == this.getColonna();
	  @*/
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
	
	//@ ensures this.puntiAttacco == \old(this.puntiAttacco) - 1;
	//@ ensures this.puntiAttacco <= 0 <==> \result == true;
	//@ ensures this.puntiAttacco > 0 <==> \result == false;
	public boolean attacca() {
		setPuntiAttacco(getPuntiAttacco() - 1);
		return getPuntiAttacco() <= 0;
	}

	/*@ also
	  @ requires p >= 1;
	  @ ensures \result == true;
	  @*/
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
