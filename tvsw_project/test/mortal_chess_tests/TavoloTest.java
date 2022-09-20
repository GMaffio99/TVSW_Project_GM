package mortal_chess_tests;

import static org.junit.Assert.*;

import java.util.ArrayList;

import org.junit.Test;

import mortal_chess.Attaccante;
import mortal_chess.AttaccanteDifensore;
import mortal_chess.Coppia;
import mortal_chess.Difensore;
import mortal_chess.Pedina;
import mortal_chess.Tavolo;

public class TavoloTest {

	@Test
	public void testGetTavolo() {
		Tavolo tavolo = Tavolo.getTavolo();
		tavolo.reset();
		assertNotNull(tavolo);
	}

	@Test
	public void testGetListaPedineAndReset() {
		Tavolo tavolo = Tavolo.getTavolo();
		tavolo.reset();
		assertTrue(tavolo.getListaPedine().isEmpty());
		tavolo.getListaPedine().put(0, null);
		assertFalse(tavolo.getListaPedine().isEmpty());
		tavolo.reset();
		assertTrue(tavolo.getListaPedine().isEmpty());
	}

	@Test
	public void testSetPuntiAndGetPuntiGiocatore() {
		Tavolo tavolo = Tavolo.getTavolo();
		tavolo.reset();
		assertEquals(tavolo.getPuntiGiocatoreX(), 10);
		assertEquals(tavolo.getPuntiGiocatoreO(), 10);
		tavolo.setPuntiGiocatoreX(3);
		tavolo.setPuntiGiocatoreO(2);
		assertEquals(tavolo.getPuntiGiocatoreX(), 3);
		assertEquals(tavolo.getPuntiGiocatoreO(), 2);
		tavolo.setPunti(5);
		assertEquals(tavolo.getPuntiGiocatoreX(), 5);
		assertEquals(tavolo.getPuntiGiocatoreO(), 5);
	}

	@Test
	public void testPartitaFinitaAndGetVincitore() {
		Tavolo tavolo = Tavolo.getTavolo();
		tavolo.reset();
		assertFalse(tavolo.partitaFinita());
		tavolo.setPuntiGiocatoreX(0);
		assertTrue(tavolo.partitaFinita());
		assertEquals(tavolo.getVincitore(), 'O');
		tavolo.setPuntiGiocatoreX(1);
		tavolo.setPuntiGiocatoreO(0);
		assertTrue(tavolo.partitaFinita());
		assertEquals(tavolo.getVincitore(), 'X');
	}
	
	@Test
	public void testCharToInt() {
		Tavolo tavolo = Tavolo.getTavolo();
		tavolo.reset();
		assertEquals(tavolo.charToInt('0'), 0);
		assertEquals(tavolo.charToInt('1'), 1);
		assertEquals(tavolo.charToInt('2'), 2);
		assertEquals(tavolo.charToInt('3'), 3);
		assertEquals(tavolo.charToInt('4'), 4);
		assertEquals(tavolo.charToInt('5'), 5);
		assertEquals(tavolo.charToInt('6'), 6);
		assertEquals(tavolo.charToInt('7'), 7);
		assertEquals(tavolo.charToInt('8'), 8);
		assertEquals(tavolo.charToInt('9'), 0);
	}
	
	@Test
	public void testIntToChar() {
		Tavolo tavolo = Tavolo.getTavolo();
		tavolo.reset();
		assertEquals(tavolo.intToChar(0), '0');
		assertEquals(tavolo.intToChar(1), '1');
		assertEquals(tavolo.intToChar(2), '2');
		assertEquals(tavolo.intToChar(3), '3');
		assertEquals(tavolo.intToChar(4), '4');
		assertEquals(tavolo.intToChar(5), '5');
		assertEquals(tavolo.intToChar(6), '6');
		assertEquals(tavolo.intToChar(7), '7');
		assertEquals(tavolo.intToChar(8), '8');
		assertEquals(tavolo.intToChar(9), '0');
	}
	
	@Test
	public void testGetIndex() {
		Tavolo tavolo = Tavolo.getTavolo();
		tavolo.reset();
		assertEquals(tavolo.getIndex('1', 'A'), 0);
		assertEquals(tavolo.getIndex(1, 'A'), 0);
		assertEquals(tavolo.getIndex('2', 'C'), 10);
		assertEquals(tavolo.getIndex(2, 'C'), 10);
		assertEquals(tavolo.getIndex('3', 'E'), 20);
		assertEquals(tavolo.getIndex(3, 'E'), 20);
		assertEquals(tavolo.getIndex('8', 'H'), 63);
		assertEquals(tavolo.getIndex(8, 'H'), 63);
	}
	
	@Test
	public void testGetPedina() {
		Tavolo tavolo = Tavolo.getTavolo();
		tavolo.reset();
		assertNull(tavolo.getPedina('1', 'A'));
		assertNull(tavolo.getPedina(1, 'A'));
		Pedina p = new Attaccante('X', 1, 'A');
		tavolo.getListaPedine().put(0, p);
		assertNotNull(tavolo.getPedina('1', 'A'));
		assertNotNull(tavolo.getPedina(1,  'A'));
		Pedina p2 = tavolo.getPedina(1,  'A');
		assertEquals(p2.getGiocatore(), 'X');
		assertEquals(p2.getRiga(), 1);
		assertEquals(p2.getColonna(), 'A');
		assertTrue(p2 instanceof Attaccante);
		Attaccante a = (Attaccante) p2;
		assertEquals(a.getPuntiAttacco(), 1);
	}

	@Test
	public void testMossaEseguibile() {
		Tavolo tavolo = Tavolo.getTavolo();
		tavolo.reset();
		
		// mossa 0 non valida
		assertFalse(tavolo.mossaEseguibile('0', 'X'));
		
		// mossa 1 eseguibile - almeno una cella libera nella prima colonna
		assertTrue(tavolo.mossaEseguibile('1', 'X'));
		
		// mossa 1 non eseguibile - nessuna cella libera nella prima colonna
		tavolo.posizionaPedina('X', 'A', '1', 'A');
		tavolo.posizionaPedina('X', 'A', '2', 'A');
		tavolo.posizionaPedina('X', 'A', '3', 'A');
		tavolo.posizionaPedina('X', 'A', '4', 'A');
		tavolo.posizionaPedina('X', 'A', '5', 'A');
		tavolo.posizionaPedina('X', 'A', '6', 'A');
		tavolo.posizionaPedina('X', 'A', '7', 'A');
		tavolo.posizionaPedina('X', 'A', '8', 'A');
		assertFalse(tavolo.mossaEseguibile('1', 'X'));
		
		// mossa 2 eseguibile - almeno una pedina movibile
		tavolo.reset();
		tavolo.posizionaPedina('X', 'A', '1', 'A');
		assertTrue(tavolo.mossaEseguibile('2', 'X'));
		
		// mossa 2 non eseguibile - nessuna pedina mobibile
		tavolo.reset();
		tavolo.posizionaPedina('X', 'A', '1', 'A');
		tavolo.posizionaPedina('O', 'A', '1', 'B');
		tavolo.posizionaPedina('O', 'A', '2', 'A');
		tavolo.posizionaPedina('O', 'A', '2', 'B');
		assertFalse(tavolo.mossaEseguibile('2', 'X'));
		
		// mossa 3 eseguibile - almeno una pedina unibile
		tavolo.reset();
		tavolo.posizionaPedina('X', 'A', '1', 'A');
		tavolo.posizionaPedina('X', 'A', '1', 'B');
		assertTrue(tavolo.mossaEseguibile('3', 'X'));
		
		// mossa 3 non eseguibile - nessuna pedina unibile
		tavolo.reset();
		tavolo.posizionaPedina('X', 'A', '1', 'A');
		tavolo.posizionaPedina('X', 'A', '3', 'A');
		assertFalse(tavolo.mossaEseguibile('3', 'X'));
		
		// mossa 4 eseguibile - almeno una pedina può attaccare una pedina
		tavolo.reset();
		tavolo.posizionaPedina('X', 'A', '1', 'A');
		tavolo.posizionaPedina('O', 'A', '1', 'B');
		assertTrue(tavolo.mossaEseguibile('4', 'X'));
		
		// mossa 4 non eseguibile - nessuna pedina può attaccare una pedina
		tavolo.reset();
		tavolo.posizionaPedina('X', 'A', '1', 'A');
		tavolo.posizionaPedina('O', 'A', '1', 'C');
		assertFalse(tavolo.mossaEseguibile('4', 'X'));
		
		// mossa 4 non eseguibile - nessuna pedina attaccante
		tavolo.reset();
		tavolo.posizionaPedina('X', 'D', '1', 'A');
		tavolo.posizionaPedina('O', 'A', '2', 'A');
		assertFalse(tavolo.mossaEseguibile('4', 'X'));
		
		// mossa 5 eseguibile - almeno una pedina può attaccare l'avversario
		tavolo.reset();
		tavolo.posizionaPedina('X', 'A', '1', 'H');
		assertTrue(tavolo.mossaEseguibile('5', 'X'));
		
		// mossa 5 non eseguibile - nessuna pedina può attaccare l'avversario
		tavolo.reset();
		tavolo.posizionaPedina('X', 'A', '1', 'A');
		assertFalse(tavolo.mossaEseguibile('5', 'X'));
		
		// mossa 5 non eseguibile - nessuna pedina attaccante
		tavolo.posizionaPedina('X', 'D', '1', 'H');
		assertFalse(tavolo.mossaEseguibile('5', 'X'));
		
		// mossa 2 non eseguibile - nessuna pedina schierata
		tavolo.reset();
		assertFalse(tavolo.mossaEseguibile('2', 'X'));
	}

	@Test
	public void testCellaOccupata() {
		Tavolo tavolo = Tavolo.getTavolo();
		tavolo.reset();
		assertFalse(tavolo.cellaOccupata('1', 'A'));
		tavolo.posizionaPedina('X', 'A', '1', 'A');
		assertTrue(tavolo.cellaOccupata('1', 'A'));
	}

	@Test
	public void testPosizionaPedina() {
		Tavolo tavolo = Tavolo.getTavolo();
		tavolo.reset();
		tavolo.posizionaPedina('O', 'D', '2', 'B');
		Pedina p = tavolo.getPedina('2', 'B');
		assertEquals(p.getGiocatore(), 'O');
		assertEquals(p.getRiga(), 2);
		assertEquals(p.getColonna(), 'B');
		assertTrue(p instanceof Difensore);
		Difensore d = (Difensore) p;
		assertEquals(d.getPuntiDifesa(), 1);
	}
	
	@Test
	public void testGetCelleAdiacenti() {
		Tavolo tavolo = Tavolo.getTavolo();
		tavolo.reset();
		ArrayList<Coppia<Integer, Character>> celleAdiacenti = tavolo.getCelleAdiacenti('2', 'B', false);
		assertEquals(celleAdiacenti.size(), 8);
		assertTrue(celleAdiacenti.contains(new Coppia<Integer, Character>(1, 'A')));
		assertTrue(celleAdiacenti.contains(new Coppia<Integer, Character>(1, 'B')));
		assertTrue(celleAdiacenti.contains(new Coppia<Integer, Character>(1, 'C')));
		assertTrue(celleAdiacenti.contains(new Coppia<Integer, Character>(2, 'A')));
		assertTrue(celleAdiacenti.contains(new Coppia<Integer, Character>(2, 'C')));
		assertTrue(celleAdiacenti.contains(new Coppia<Integer, Character>(3, 'A')));
		assertTrue(celleAdiacenti.contains(new Coppia<Integer, Character>(3, 'B')));
		assertTrue(celleAdiacenti.contains(new Coppia<Integer, Character>(3, 'C')));
		celleAdiacenti = tavolo.getCelleAdiacenti('2', 'B', true);
		assertEquals(celleAdiacenti.size(), 4);
		assertTrue(celleAdiacenti.contains(new Coppia<Integer, Character>(1, 'B')));
		assertTrue(celleAdiacenti.contains(new Coppia<Integer, Character>(2, 'A')));
		assertTrue(celleAdiacenti.contains(new Coppia<Integer, Character>(2, 'C')));
		assertTrue(celleAdiacenti.contains(new Coppia<Integer, Character>(3, 'B')));
		celleAdiacenti = tavolo.getCelleAdiacenti('8', 'H', false);
		assertEquals(celleAdiacenti.size(), 3);
		assertTrue(celleAdiacenti.contains(new Coppia<Integer, Character>(7, 'G')));
		assertTrue(celleAdiacenti.contains(new Coppia<Integer, Character>(7, 'H')));
		assertTrue(celleAdiacenti.contains(new Coppia<Integer, Character>(8, 'G')));
		celleAdiacenti = tavolo.getCelleAdiacenti('8', 'H', true);
		assertEquals(celleAdiacenti.size(), 2);
		assertTrue(celleAdiacenti.contains(new Coppia<Integer, Character>(7, 'H')));
		assertTrue(celleAdiacenti.contains(new Coppia<Integer, Character>(8, 'G')));
	}

	@Test
	public void testPedinaMovibile() {
		Tavolo tavolo = Tavolo.getTavolo();
		tavolo.reset();
		// return 2 - nessuna pedina nella cella
		assertEquals(tavolo.pedinaMovibile('X', '1', 'A'), 2);
		// return -1 - pedina appartenente al giocatore avversario
		tavolo.posizionaPedina('X', 'A', '1', 'A');
		assertEquals(tavolo.pedinaMovibile('O', '1', 'A'), -1);
		// return 0 - pedina movibile
		assertEquals(tavolo.pedinaMovibile('X', '1', 'A'), 0);
		// return 1 - pedina non movibile per celle adiacenti occupate
		tavolo.posizionaPedina('X', 'A', '1', 'B');
		tavolo.posizionaPedina('X', 'D', '2', 'A');
		tavolo.posizionaPedina('X', 'A', '2', 'B');
		assertEquals(tavolo.pedinaMovibile('X', '1', 'A'), 1);
	}

	@Test
	public void testCellaRaggiungibile() {
		Tavolo tavolo = Tavolo.getTavolo();
		tavolo.reset();
		tavolo.posizionaPedina('X', 'A', '1', 'A');
		// return -1 - cella non raggiungibile perchè non adiacente
		assertEquals(tavolo.cellaRaggiungibile('1', 'A', '3', 'A'), -1);
		// return 1 - cella non raggiungibile perchè occupata
		tavolo.posizionaPedina('X', 'A', '2', 'A');
		assertEquals(tavolo.cellaRaggiungibile('1', 'A', '2', 'A'), 1);
		// return 0 - cella raggiungibile
		assertEquals(tavolo.cellaRaggiungibile('1', 'A', '1', 'B'), 0);
	}

	@Test
	public void testMuoviPedina() {
		Tavolo tavolo = Tavolo.getTavolo();
		tavolo.reset();
		
		tavolo.posizionaPedina('X', 'A', '1', 'A');
		assertEquals(tavolo.getListaPedine().get(0).getRiga(), 1);
		assertEquals(tavolo.getListaPedine().get(0).getColonna(), 'A');
		Pedina p = new Attaccante('X', 1, 'A');
		assertTrue(tavolo.getListaPedine().get(0).equals(p));
		
		tavolo.muoviPedina('1', 'A', '2', 'B');
		assertNull(tavolo.getListaPedine().get(0));
		assertEquals(tavolo.getListaPedine().get(9).getRiga(), 2);
		assertEquals(tavolo.getListaPedine().get(9).getColonna(), 'B');
		assertFalse(tavolo.getListaPedine().get(9).equals(p));
	}

	@Test
	public void testPedinaUnibile() {
		Tavolo tavolo = Tavolo.getTavolo();
		tavolo.reset();
		// return 2 - nessuna pedina nella cella
		assertEquals(tavolo.pedinaUnibile('X', '1', 'A'), 2);
		// return -1 - pedina appartenente al giocatore avversario
		tavolo.posizionaPedina('X', 'A', '1', 'A');
		assertEquals(tavolo.pedinaUnibile('O', '1', 'A'), -1);
		// return 1 - nessuna pedina adiacente da poter unire
		assertEquals(tavolo.pedinaUnibile('X', '1', 'A'), 1);
		// return 0 - pedina unibile
		tavolo.posizionaPedina('X', 'D', '2', 'A');
		assertEquals(tavolo.pedinaUnibile('X', '1', 'A'), 0);
	}

	@Test
	public void testPedineUnibili() {
		Tavolo tavolo = Tavolo.getTavolo();
		tavolo.reset();
		// return 2 - nessuna pedina nella cella
		assertEquals(tavolo.pedineUnibili('X', '1', 'A', '2', 'A'), 2);
		// return -1 - pedina appartenente al giocatore avversario
		tavolo.posizionaPedina('X', 'A', '2', 'A');
		assertEquals(tavolo.pedineUnibili('O', '1', 'A', '2', 'A'), -1);
		// return 1 - pedine non adiacenti
		assertEquals(tavolo.pedineUnibili('X', '1', 'H', '2', 'A'), 1);
		// return 0 - pedine unibili
		assertEquals(tavolo.pedineUnibili('X', '1', 'A', '2', 'A'), 0);
	}

	@Test
	public void testUnisciPedine() {
		Tavolo tavolo = Tavolo.getTavolo();
		tavolo.reset();
		
		Pedina p1 = new Attaccante('X', 1, 'A');
		Pedina p2 = new Difensore('X', 2, 'A');
		tavolo.posizionaPedina('X', 'A', '1', 'A');
		tavolo.posizionaPedina('X', 'D', '2', 'A');
		assertNotNull(tavolo.getListaPedine().get(0));
		assertTrue(tavolo.getListaPedine().get(0).equals(p1));
		assertNotNull(tavolo.getListaPedine().get(8));
		assertTrue(tavolo.getListaPedine().get(8).equals(p2));
		
		Pedina p3 = new AttaccanteDifensore('X', 1, 'A', 1, 1);
		tavolo.unisciPedine('1', 'A', '2', 'A');
		assertNotNull(tavolo.getListaPedine().get(0));
		assertTrue(tavolo.getListaPedine().get(0).equals(p3));
		assertNull(tavolo.getListaPedine().get(8));
	}

	@Test
	public void testPedinaAttaccante() {
		Tavolo tavolo = Tavolo.getTavolo();
		tavolo.reset();
		// return 2 - nessuna pedina nella cella
		assertEquals(tavolo.pedinaAttaccante('X', '1', 'A'), 2);
		// return -1 - pedina appartenente all'avversario
		tavolo.posizionaPedina('X', 'A', '1', 'A');
		assertEquals(tavolo.pedinaAttaccante('O', '1', 'A'), -1);
		// return 3 - pedina non attaccante
		tavolo.posizionaPedina('X', 'D', '1', 'H');
		assertEquals(tavolo.pedinaAttaccante('X', '1', 'H'), 3);
		// return 1 - pedina non ha avversari adiacenti
		assertEquals(tavolo.pedinaAttaccante('X', '1', 'A'), 1);
		// return 0 - pedina può attaccare
		tavolo.posizionaPedina('O', 'D', '1', 'B');
		assertEquals(tavolo.pedinaAttaccante('X', '1', 'A'), 0);
	}

	@Test
	public void testPedinaAttaccabile() {
		Tavolo tavolo = Tavolo.getTavolo();
		tavolo.reset();
		// return 2 - nessuna pedina nella cella
		assertEquals(tavolo.pedinaAttaccabile('X', '1', 'A', '1', 'B'), 2);
		// return -1 - pedina da attaccare non appartenente all'avversario
		tavolo.posizionaPedina('X', 'D', '2', 'A');
		assertEquals(tavolo.pedinaAttaccabile('X', '1', 'A', '2', 'A'), -1);
		// return 1 - pedina da attaccare non adiacente
		tavolo.posizionaPedina('O', 'D', '1', 'H');
		assertEquals(tavolo.pedinaAttaccabile('X', '1', 'A', '1', 'H'), 1);
		// return 0 - pedina attaccabile
		tavolo.posizionaPedina('O', 'D', '1', 'B');
		assertEquals(tavolo.pedinaAttaccabile('X', '1', 'A', '1', 'B'), 0);
	}

	@Test
	public void testAttaccaPedina() {
		Tavolo tavolo = Tavolo.getTavolo();
		tavolo.reset();
		// pedina attaccante AD non esaurisce punti attacco, pedina attaccata esaurisce punti difesa
		tavolo.getListaPedine().put(0, new AttaccanteDifensore('X', 1, 'A', 2, 1));
		tavolo.getListaPedine().put(1, new Difensore('O', 1, 'B', 3));
		tavolo.attaccaPedina('1', 'A', '1', 'B');
		AttaccanteDifensore ad = (AttaccanteDifensore) tavolo.getListaPedine().get(0);
		assertEquals(ad.getPuntiAttacco(), 1);
		Difensore d = (Difensore) tavolo.getListaPedine().get(1);
		assertNotNull(d);
		assertEquals(d.getPuntiDifesa(), 1);
		// pedina attaccante AD esaurisce punti attacco, pedina attaccata esaurisce punti difesa
		tavolo.attaccaPedina('1', 'A', '1', 'B');
		Pedina p = tavolo.getListaPedine().get(0);
		assertTrue(p instanceof Difensore);
		assertNull(tavolo.getListaPedine().get(1));
		// pedina attaccante A non esaurisce punti attacco, pedina attaccata esaurisce punti difesa
		tavolo.getListaPedine().put(63, new Attaccante('O', 8, 'H', 2));
		tavolo.getListaPedine().put(55, new Difensore('X', 7, 'H', 3));
		tavolo.attaccaPedina('8', 'H', '7', 'H');
		Attaccante a = (Attaccante) tavolo.getListaPedine().get(63);
		assertEquals(a.getPuntiAttacco(), 1);
		d = (Difensore) tavolo.getListaPedine().get(55);
		assertNotNull(d);
		assertEquals(d.getPuntiDifesa(), 1);
		// pedina attaccante A esaurisce punti attacco, pedina attaccata esaurisce punti difesa
		tavolo.attaccaPedina('8', 'H', '7', 'H');
		assertNull(tavolo.getListaPedine().get(63));
		assertNull(tavolo.getListaPedine().get(55));
	}

	@Test
	public void testPedinaAttaccanteAvversario() {
		Tavolo tavolo = Tavolo.getTavolo();
		tavolo.reset();
		// return 2 - nessuna pedina nella cella
		assertEquals(tavolo.pedinaAttaccanteAvversario('X', '1', 'H'), 2);
		// return -1 - pedina appartenente all'avversario
		tavolo.posizionaPedina('O', 'A', '1', 'A');
		assertEquals(tavolo.pedinaAttaccanteAvversario('X', '1', 'A'), -1);
		// return 3 - pedina non attaccante
		tavolo.posizionaPedina('X', 'D', '8', 'H');
		assertEquals(tavolo.pedinaAttaccanteAvversario('X', '8', 'H'), 3);
		// return 1 - pedina non può attaccare l'avversario
		tavolo.posizionaPedina('X', 'A', '1', 'G');
		assertEquals(tavolo.pedinaAttaccanteAvversario('X', '1', 'G'), 1);
		// return 0 - pedina può attaccare l'avversario
		tavolo.posizionaPedina('X', 'A', '1', 'H');
		assertEquals(tavolo.pedinaAttaccanteAvversario('X', '1', 'H'), 0);
	}

	@Test
	public void testAttaccaAvversario() {
		Tavolo tavolo = Tavolo.getTavolo();
		tavolo.reset();
		// pedina attaccante AD non esaurisce punti attacco
		tavolo.getListaPedine().put(7, new AttaccanteDifensore('X', 1, 'H', 2, 1));
		tavolo.attaccaAvversario('X', '1', 'H');
		AttaccanteDifensore ad = (AttaccanteDifensore) tavolo.getListaPedine().get(7);
		assertEquals(ad.getPuntiAttacco(), 1);
		assertEquals(tavolo.getPuntiGiocatoreO(), 8);
		// pedina attaccante AD esaurisce punti attacco
		tavolo.attaccaAvversario('X', '1', 'H');
		Pedina p = tavolo.getListaPedine().get(7);
		assertTrue(p instanceof Difensore);
		assertEquals(tavolo.getPuntiGiocatoreO(), 7);
		// pedina attaccante A non esaurisce punti attacco
		tavolo.getListaPedine().put(56, new Attaccante('O', 8, 'A', 2));
		tavolo.attaccaAvversario('O', '8', 'A');
		Attaccante a = (Attaccante) tavolo.getListaPedine().get(56);
		assertEquals(a.getPuntiAttacco(), 1);
		assertEquals(tavolo.getPuntiGiocatoreX(), 8);
		// pedina attaccante A esaurisce punti attacco
		tavolo.attaccaAvversario('O', '8', 'A');
		assertNull(tavolo.getListaPedine().get(56));
		assertEquals(tavolo.getPuntiGiocatoreX(), 7);
	}

	@Test
	public void testDiminuisciPuntiGiocatore() {
		Tavolo tavolo = Tavolo.getTavolo();
		tavolo.reset();
		assertEquals(tavolo.getPuntiGiocatoreX(), 10);
		assertEquals(tavolo.getPuntiGiocatoreO(), 10);
		tavolo.diminuisciPuntiGiocatore('X', 5);
		assertEquals(tavolo.getPuntiGiocatoreO(), 5);
		tavolo.diminuisciPuntiGiocatore('O', 7);
		assertEquals(tavolo.getPuntiGiocatoreX(), 3);
	}

}
