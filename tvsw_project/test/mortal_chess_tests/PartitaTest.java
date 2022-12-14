package mortal_chess_tests;

import static org.junit.Assert.*;

import java.io.BufferedReader;
import java.io.IOException;

import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;
import static org.mockito.Mockito.*;

import mortal_chess.Attaccante;
import mortal_chess.Difensore;
import mortal_chess.Partita;
import mortal_chess.Tavolo;
import mortal_chess.TavoloUtils;

public class PartitaTest {

	static Tavolo tavolo;
	static BufferedReader mockReader;
	static Partita partita;
	
	@BeforeClass
	public static void setupPartita() {
		mockReader = mock(BufferedReader.class);
		tavolo = Tavolo.getTavolo();
		partita = new Partita(mockReader, tavolo);
	}
	
	@Before
	public void resetMockReaderAndTavolo() throws IOException {
		mockReader.reset();
		tavolo.reset();
	}
	
	@Test
	public void testCostruttorePartita() {
		assertNotNull(new Partita(mockReader, tavolo));
	}
	
	@Test
	public void testSelezioneCella() throws IOException {
		// setup mocked input reader
		when(mockReader.readLine()).thenReturn("") // no stringa vuota
								   .thenReturn("A") // no stringa di 1 carattere
								   .thenReturn("A0") // no riga 0
								   .thenReturn("I1") // no colonna I
								   .thenReturn("A10") // no stringa di 3 caratteri
								   .thenReturn("A1"); // ok
		//test
		assertEquals(partita.selezioneCella("SELEZIONA CELLA"), "A1");
	}

	@Test
	public void testImpostaPunti() throws IOException {
		// setup mocked input reader
		when(mockReader.readLine()).thenReturn("dieci") // no numero testuale
								   .thenReturn("-10") // no numero negativo
								   .thenReturn("0") // no numero nullo
								   .thenReturn("5"); // ok
		// test
		partita.impostaPunti();
		assertEquals(tavolo.getPuntiGiocatoreX(), 5);
		assertEquals(tavolo.getPuntiGiocatoreO(), 5);
		
		// setup mocked input reader
		mockReader.reset();
		when(mockReader.readLine()).thenReturn("20"); // ok
		// test
		partita.impostaPunti();
		assertEquals(tavolo.getPuntiGiocatoreX(), 20);
		assertEquals(tavolo.getPuntiGiocatoreO(), 20);
	}

	@Test
	public void testSelezionaMossa() throws IOException {
		// setup mocked input reader
		when(mockReader.readLine()).thenReturn("0") // no mossa < 1
								   .thenReturn("6") // no mossa > 5
								   .thenReturn("11") // no mossa > 5
								   .thenReturn("") // no stringa vuota
								   .thenReturn(" ") // no stringa spazio
								   .thenReturn("A") // no lettera
								   .thenReturn("1"); // ok
		assertEquals(partita.selezionaMossa('X', "SELEZIONA MOSSA"), '1');
		
		mockReader.reset();
		when(mockReader.readLine()).thenReturn("2"); // ok
		tavolo.getListaPedine().put(TavoloUtils.getIndex(1, 'H'), new Attaccante('X', 1, 'H'));
		assertEquals(partita.selezionaMossa('X', "SELEZIONA MOSSA"), '2');
		
		mockReader.reset();
		when(mockReader.readLine()).thenReturn("3"); // ok
		tavolo.getListaPedine().put(TavoloUtils.getIndex(2, 'H'), new Attaccante('X', 2, 'H'));
		assertEquals(partita.selezionaMossa('X', "SELEZIONA MOSSA"), '3');
		
		mockReader.reset();
		when(mockReader.readLine()).thenReturn("4"); // ok
		tavolo.getListaPedine().put(TavoloUtils.getIndex(3, 'H'), new Difensore('O', 3, 'H'));
		assertEquals(partita.selezionaMossa('X', "SELEZIONA MOSSA"), '4');
		
		mockReader.reset();
		when(mockReader.readLine()).thenReturn("5"); // ok
		assertEquals(partita.selezionaMossa('X', "SELEZIONA MOSSA"), '5');
	}

	@Test
	public void testPosizionarePedina() throws IOException {
		// setup mocked input reader
		when(mockReader.readLine()).thenReturn("Attaccante") // no stringa "Attaccante"
								   .thenReturn("Difensore") // no stringa "Difensore"
								   .thenReturn("AD") // no AttaccanteDifensore
								   .thenReturn("A") // ok
								   .thenReturn("B1") // no colonna 'B' per giocatore X
								   .thenReturn("A1") // cella occupata
								   .thenReturn("A2"); // ok
		// setup tavolo
		tavolo.getListaPedine().put(TavoloUtils.getIndex(1, 'A'), new Attaccante('X', 1, 'A'));
		// test
		assertNull(tavolo.getPedina('2', 'A'));
		partita.posizionarePedina('X', "[X]");
		assertNotNull(tavolo.getPedina('2', 'A'));
		
		// setup mocked input reader
		mockReader.reset();
		when(mockReader.readLine()).thenReturn("D") // ok
								   .thenReturn("H8"); // ok
		// test
		assertNull(tavolo.getPedina('8', 'H'));
		partita.posizionarePedina('O', "[O]");
		assertNotNull(tavolo.getPedina('8', 'H'));
	}

	@Test
	public void testMuoverePedina() throws IOException {
		// setup mocked input reader
		when(mockReader.readLine()).thenReturn("H1") // pedina appartenente all'avversario
								   .thenReturn("A1") // pedina non pu? essere mossa
								   .thenReturn("A6") // cella vuota
								   .thenReturn("A7") // ok
								   .thenReturn("C7") // cella non raggiungibile
								   .thenReturn("A8") // cella occupata
								   .thenReturn("B7"); // ok
		// setup tavolo
		tavolo.getListaPedine().put(TavoloUtils.getIndex(1, 'H'), new Attaccante('O', 1, 'H'));
		tavolo.getListaPedine().put(TavoloUtils.getIndex(1, 'A'), new Attaccante('X', 1, 'A'));
		tavolo.getListaPedine().put(TavoloUtils.getIndex(2, 'A'), new Attaccante('X', 2, 'A'));
		tavolo.getListaPedine().put(TavoloUtils.getIndex(1, 'B'), new Attaccante('X', 1, 'B'));
		tavolo.getListaPedine().put(TavoloUtils.getIndex(2, 'B'), new Attaccante('X', 2, 'B'));
		tavolo.getListaPedine().put(TavoloUtils.getIndex(7, 'A'), new Attaccante('X', 7, 'A'));
		tavolo.getListaPedine().put(TavoloUtils.getIndex(8, 'A'), new Attaccante('X', 8, 'A'));
		// test
		assertNotNull(tavolo.getPedina('7', 'A'));
		assertNull(tavolo.getPedina('7', 'B'));
		partita.muoverePedina('X', "[X]");
		assertNull(tavolo.getPedina('7', 'A'));
		assertNotNull(tavolo.getPedina('7', 'B'));
		
		// setup mocked input reader
		mockReader.reset();
		when(mockReader.readLine()).thenReturn("H1") // ok
								   .thenReturn("G2"); // ok
		// test
		assertNotNull(tavolo.getPedina('1', 'H'));
		assertNull(tavolo.getPedina('2', 'G'));
		partita.muoverePedina('O', "[O]");
		assertNull(tavolo.getPedina('1', 'H'));
		assertNotNull(tavolo.getPedina('2', 'G'));
	}

	@Test
	public void testUnirePedine() throws IOException {
		// setup mocked input reader
		when(mockReader.readLine()).thenReturn("H1") // pedina appartenente all'avversario
								   .thenReturn("A1") // pedina non pu? essere unita
								   .thenReturn("A2") // cella vuota
								   .thenReturn("A7") // ok
								   .thenReturn("B7") // pedina appartenente all'avversario
								   .thenReturn("A5") // pedine non adiacenti
								   .thenReturn("A6") // cella vuota
								   .thenReturn("A8"); // ok
		// setup tavolo
		tavolo.getListaPedine().put(TavoloUtils.getIndex(1, 'H'), new Attaccante('O', 1, 'H'));
		tavolo.getListaPedine().put(TavoloUtils.getIndex(1, 'A'), new Attaccante('X', 1, 'A'));
		tavolo.getListaPedine().put(TavoloUtils.getIndex(7, 'A'), new Attaccante('X', 7, 'A'));
		tavolo.getListaPedine().put(TavoloUtils.getIndex(7, 'B'), new Attaccante('O', 7, 'B'));
		tavolo.getListaPedine().put(TavoloUtils.getIndex(5, 'A'), new Attaccante('X', 5, 'A'));
		tavolo.getListaPedine().put(TavoloUtils.getIndex(8, 'A'), new Attaccante('X', 8, 'A'));
		// test
		assertNotNull(tavolo.getPedina('7', 'A'));
		assertNotNull(tavolo.getPedina('8', 'A'));
		partita.unirePedine('X', "[X]");
		assertNotNull(tavolo.getPedina('7', 'A'));
		assertNull(tavolo.getPedina('8', 'A'));
		
		// setup mocked input reader
		mockReader.reset();
		when(mockReader.readLine()).thenReturn("H1") // ok
								   .thenReturn("H2"); // ok
		// setup tavolo
		tavolo.getListaPedine().put(TavoloUtils.getIndex(2, 'H'), new Attaccante('O', 2, 'H'));
		// test
		assertNotNull(tavolo.getPedina('1', 'H'));
		assertNotNull(tavolo.getPedina('2', 'H'));
		partita.unirePedine('O', "[O]");
		assertNotNull(tavolo.getPedina('1', 'H'));
		assertNull(tavolo.getPedina('2', 'H'));
	}

	@Test
	public void testAttaccarePedina() throws IOException {
		// setup mocked input reader
		when(mockReader.readLine()).thenReturn("H1") // pedina appartenente all'avversario
								   .thenReturn("A1") // pedina non ha avversari adiacenti
								   .thenReturn("A2") // cella vuota
								   .thenReturn("A3") // pedina non attaccante
								   .thenReturn("A7") // ok
								   .thenReturn("A8") // pedina non appartenente all'avversario
								   .thenReturn("C7") // pedine non attaccabile
								   .thenReturn("A6") // cella vuota
								   .thenReturn("B7"); // ok
		// setup tavolo
		tavolo.getListaPedine().put(TavoloUtils.getIndex(1, 'H'), new Attaccante('O', 1, 'H'));
		tavolo.getListaPedine().put(TavoloUtils.getIndex(1, 'A'), new Attaccante('X', 1, 'A'));
		tavolo.getListaPedine().put(TavoloUtils.getIndex(3, 'A'), new Difensore('X', 3, 'A'));
		tavolo.getListaPedine().put(TavoloUtils.getIndex(7, 'A'), new Attaccante('X', 7, 'A'));
		tavolo.getListaPedine().put(TavoloUtils.getIndex(8, 'A'), new Attaccante('X', 8, 'A'));
		tavolo.getListaPedine().put(TavoloUtils.getIndex(7, 'C'), new Attaccante('O', 7, 'C'));
		tavolo.getListaPedine().put(TavoloUtils.getIndex(7, 'B'), new Attaccante('O', 7, 'B'));
		// test
		assertNotNull(tavolo.getPedina('7', 'A'));
		assertNotNull(tavolo.getPedina('7', 'B'));
		partita.attaccarePedina('X', "[X]");
		assertNull(tavolo.getPedina('7', 'A'));
		assertNull(tavolo.getPedina('7', 'B'));
		
		// setup mocked input reader
		mockReader.reset();
		when(mockReader.readLine()).thenReturn("B3") // ok
								   .thenReturn("A3"); // ok
		// setup tavolo
		tavolo.getListaPedine().put(TavoloUtils.getIndex(3, 'B'), new Attaccante('O', 3, 'B'));
		// test
		assertNotNull(tavolo.getPedina('3', 'B'));
		assertNotNull(tavolo.getPedina('3', 'A'));
		partita.attaccarePedina('O', "[O]");
		assertNull(tavolo.getPedina('3', 'B'));
		assertNull(tavolo.getPedina('3', 'A'));
	}

	@Test
	public void testAttaccareAvversario() throws IOException {
		// setup mocked input reader
		when(mockReader.readLine()).thenReturn("A8") // pedina appartenente all'avversario
								   .thenReturn("A1") // pedina non pu? attaccare l'avversario
								   .thenReturn("H2") // cella vuota
								   .thenReturn("H3") // pedina non attaccante
								   .thenReturn("H4"); // ok
		// setup tavolo
		tavolo.getListaPedine().put(TavoloUtils.getIndex(8, 'A'), new Attaccante('O', 8, 'A'));
		tavolo.getListaPedine().put(TavoloUtils.getIndex(1, 'A'), new Attaccante('X', 1, 'A'));
		tavolo.getListaPedine().put(TavoloUtils.getIndex(3, 'H'), new Difensore('X', 3, 'H'));
		tavolo.getListaPedine().put(TavoloUtils.getIndex(4, 'H'), new Attaccante('X', 4, 'H'));
		// test
		assertNotNull(tavolo.getPedina('4', 'H'));
		assertEquals(tavolo.getPuntiGiocatoreO(), 10);
		partita.attaccareAvversario('X', "[X]");
		assertNull(tavolo.getPedina('4', 'H'));
		assertEquals(tavolo.getPuntiGiocatoreO(), 9);
		
		// setup mocked input reader
		mockReader.reset();
		when(mockReader.readLine()).thenReturn("A8"); // ok
		// test
		assertNotNull(tavolo.getPedina('8', 'A'));
		assertEquals(tavolo.getPuntiGiocatoreX(), 10);
		partita.attaccareAvversario('O', "[O]");
		assertNull(tavolo.getPedina('8', 'A'));
		assertEquals(tavolo.getPuntiGiocatoreO(), 9);
	}

}
