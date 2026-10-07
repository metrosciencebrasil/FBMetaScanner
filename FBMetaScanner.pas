{******************************************************************************
  FBMetaScanner - Delphi 12 / VCL / FireDAC / Firebird 5

  Componente visual que procura possiveis causas do erro:
    [FireDAC][Phys][FB] Dynamic SQL Error. SQL error code = -817
    Metadata update statement is not allowed by the current database SQL dialect 3

  Modos de varredura:
    1) Form      - inspeciona os componentes VIVOS do form (e DataModules abertos)
    2) Unit      - le uma .pas (e a .dfm correspondente) escolhida pelo usuario
    3) Projeto   - le recursivamente todas as .pas / .dfm (e FDConnectionDefs.ini)

  Uso rapido (em tempo de execucao, sem instalar pacote):
    uses FBMetaScanner;
    with TFBMetaScanner.Create(Self) do
    begin
      Parent := Self;
      Align  := alClient;
    end;

  Para instalar na paleta: adicione esta unit a um pacote de design-time
  (requires: rtl, vcl, FireDAC, FireDACCommonDriver, FireDACCommon,
   FireDACPhysFBDriver, designide) e instale. Aparece na aba "Diagnostico".
******************************************************************************}
unit FBMetaScanner;

interface

uses
  System.SysUtils, System.Classes, System.StrUtils, System.IOUtils,
  System.RegularExpressions, System.Generics.Collections,
  System.Generics.Defaults, System.Variants,
  Winapi.Windows,
  Vcl.Controls, Vcl.Forms, Vcl.StdCtrls, Vcl.ExtCtrls, Vcl.ComCtrls,
  Vcl.Dialogs, Vcl.Clipbrd, Vcl.Graphics,
  FireDAC.Stan.Intf, FireDAC.Stan.Option,
  FireDAC.Phys.FB, FireDAC.Comp.Client, FireDAC.Comp.Script;

type
  TFBSeverity = (fsError, fsWarning, fsInfo);

  TFBFinding = record
    Severity: TFBSeverity;
    Source: string;
    Line: Integer;
    Msg: string;
    Fix: string;
  end;

  TFBMetaScanner = class(TCustomPanel)
  private
    FConnection: TFDConnection;
    FTargetForm: TCustomForm;
    FProjectDir: string;
    FIncludeDataModules: Boolean;
    FFindings: TList<TFBFinding>;
    FSeen: TList<TComponent>;
    FCurSource: string;
    FRootDir: string;
    FFoundFBConn: Boolean;
    FFoundLink: Boolean;
    // UI
    FTop: TPanel;
    FBtnForm, FBtnUnit, FBtnProject, FBtnCopy, FBtnClear: TButton;
    FStatus: TLabel;
    FList: TListView;
    FDetail: TMemo;

    procedure SetConnection(const Value: TFDConnection);
    procedure SetTargetForm(const Value: TCustomForm);
    function MakeButton(const ACaption: string; ALeft, AWidth: Integer;
      AHandler: TNotifyEvent): TButton;
    procedure BtnFormClick(Sender: TObject);
    procedure BtnUnitClick(Sender: TObject);
    procedure BtnProjectClick(Sender: TObject);
    procedure BtnCopyClick(Sender: TObject);
    procedure BtnClearClick(Sender: TObject);
    procedure ListSelectItem(Sender: TObject; Item: TListItem; Selected: Boolean);
    procedure ListCustomDrawItem(Sender: TCustomListView; Item: TListItem;
      State: TCustomDrawState; var DefaultDraw: Boolean);

    procedure BeginScan;
    procedure EndScan;
    procedure RefreshList;
    procedure SetBusy(ABusy: Boolean; const AText: string = '');
    procedure AddFinding(ASev: TFBSeverity; const ASource: string; ALine: Integer;
      const AMsg, AFix: string);

    // varredura viva
    procedure ScanComponents(AOwner: TComponent; const APath: string);
    procedure CheckComponent(C: TComponent; const AWhere: string);
    procedure CheckConnection(AConn: TFDConnection; const AWhere: string);
    procedure CheckLiveDatabase(AConn: TFDConnection; const AWhere: string);
    procedure CheckTransaction(ATx: TFDTransaction; const AWhere: string);
    procedure CheckDriverLink(ALink: TFDPhysFBDriverLink; const AWhere: string);
    procedure CheckLoadedClient;
    procedure CheckClientLib(const APath, AWhere: string; ALine: Integer);
    function ResolveLib(const APath: string): string;

    // varredura de arquivos
    procedure ScanFile(const AFile: string);
    procedure ScanPas(ALines: TStrings);
    procedure ScanDfm(ALines: TStrings);
    procedure ScanIni(ALines: TStrings);
    procedure AnalyzeDfmBlock(const ACls, AName: string; ABlock: TStrings;
      AStartLine: Integer);
    function ScanSQLLines(ALines: TStrings; const AWhere: string;
      ABaseLine: Integer; AComponentMode, AMultiOK: Boolean): Integer;
    function RelName(const AFile: string): string;
  protected
    procedure Notification(AComponent: TComponent; Operation: TOperation); override;
  public
    constructor Create(AOwner: TComponent); override;
    destructor Destroy; override;

    procedure ScanForm;
    procedure ScanUnit(const AFileName: string = '');
    procedure ScanProject(const ADir: string = '');
    procedure Clear;
    function ReportText: string;
    function ErrorCount: Integer;
  published
    /// Conexao a inspecionar alem das encontradas no form (opcional)
    property Connection: TFDConnection read FConnection write SetConnection;
    /// Form a varrer; se vazio usa o form onde o componente esta
    property TargetForm: TCustomForm read FTargetForm write SetTargetForm;
    /// Pasta do projeto; se vazio o botao Projeto pergunta
    property ProjectDir: string read FProjectDir write FProjectDir;
    /// Inclui os TDataModule abertos na varredura do form
    property IncludeDataModules: Boolean read FIncludeDataModules
      write FIncludeDataModules default True;
    property Align;
    property Anchors;
    property Visible;
    property Enabled;
  end;

procedure Register;

implementation

const
  RX_DDL = '\b(CREATE|ALTER|DROP|RECREATE)\s+(OR\s+ALTER\s+)?(GLOBAL\s+TEMPORARY\s+)?' +
    '(TABLE|VIEW|PROCEDURE|TRIGGER|DOMAIN|INDEX|GENERATOR|SEQUENCE|EXCEPTION|' +
    'FUNCTION|PACKAGE|ROLE)\b';
  RX_SYSTAB = '\b(UPDATE|DELETE\s+FROM|INSERT\s+INTO)\s+RDB\$\w+';
  RX_SETDIALECT = '\bSET\s+SQL\s+DIALECT\b';
  RX_ALTERDB = '\bALTER\s+DATABASE\b';
  RX_DIALECT = 'Dialect[''"\]\s]*[:=]+\s*[''"]?(\d)';
  RX_DML = '\b(INSERT\s+INTO|DELETE\s+FROM)\b|(?<!\bON\s)\bUPDATE\s+\w';
  RX_COMMIT = '\bCommit(Retaining)?\b';
  RX_TYPES = '\b(BIGINT|DATE|TIME|TIMESTAMP|DECIMAL|NUMERIC)\b';

  SevText: array[TFBSeverity] of string = ('ERRO', 'AVISO', 'INFO');

  FIX_DIALECT = 'No TFDConnection (Params) use Dialect=3 e confirme que o proprio banco ' +
    'esta em dialeto 3: "select MON$SQL_DIALECT from MON$DATABASE". Se o banco estiver ' +
    'em dialeto 1, converta com: gfix -sql_dialect 3 <banco> (revise tipos DATE/NUMERIC antes).';
  FIX_RO = 'Defina ReadOnly=False e execute o DDL numa transacao de escrita ' +
    '(TxOptions.ReadOnly / TFDTransaction.Options.ReadOnly = False).';
  FIX_DDL = 'DDL exige transacao de escrita, banco em dialeto 3 e Commit logo apos executar. ' +
    'Prefira TFDScript (ou um TFDCommand por comando) separado dos comandos de dados.';

procedure Register;
begin
  RegisterComponents('Diagnostico', [TFBMetaScanner]);
end;

{ ---------------------------- helpers de arquivo ---------------------------- }

function GetFileVer(const AFile: string; out AMajor, AMinor, ARel, ABuild: Word): Boolean;
var
  Sz, H: DWORD;
  Buf: TBytes;
  P: Pointer;
  Len: UINT;
  Info: PVSFixedFileInfo;
begin
  Result := False;
  Sz := GetFileVersionInfoSize(PChar(AFile), H);
  if Sz = 0 then Exit;
  SetLength(Buf, Sz);
  if not GetFileVersionInfo(PChar(AFile), 0, Sz, @Buf[0]) then Exit;
  if not VerQueryValue(@Buf[0], '\', P, Len) then Exit;
  Info := PVSFixedFileInfo(P);
  AMajor := HiWord(Info^.dwFileVersionMS);
  AMinor := LoWord(Info^.dwFileVersionMS);
  ARel := HiWord(Info^.dwFileVersionLS);
  ABuild := LoWord(Info^.dwFileVersionLS);
  Result := True;
end;

function GetPEBits(const AFile: string): Integer;
var
  FS: TFileStream;
  Off: Int32;
  Sig: UInt32;
  Mach: UInt16;
begin
  Result := 0;
  try
    FS := TFileStream.Create(AFile, fmOpenRead or fmShareDenyNone);
    try
      FS.Position := $3C;
      FS.ReadBuffer(Off, 4);
      FS.Position := Off;
      FS.ReadBuffer(Sig, 4);
      if Sig <> $00004550 then Exit;
      FS.ReadBuffer(Mach, 2);
      case Mach of
        $014C: Result := 32;
        $8664: Result := 64;
      end;
    finally
      FS.Free;
    end;
  except
    Result := 0;
  end;
end;

function IsBinaryDfm(const AFile: string): Boolean;
var
  FS: TFileStream;
  Sig: array[0..3] of AnsiChar;
begin
  Result := False;
  try
    FS := TFileStream.Create(AFile, fmOpenRead or fmShareDenyNone);
    try
      if FS.Size < 4 then Exit;
      FS.ReadBuffer(Sig, 4);
      Result := (Sig[0] = 'T') and (Sig[1] = 'P') and (Sig[2] = 'F') and (Sig[3] = '0');
    finally
      FS.Free;
    end;
  except
    Result := False;
  end;
end;

function IsRelevantClass(const ACls: string): Boolean;
begin
  Result := MatchText(ACls, ['TFDConnection', 'TFDTransaction',
    'TFDPhysFBDriverLink', 'TFDQuery', 'TFDCommand', 'TFDScript']);
end;

function LineOf(ABase, AIndex: Integer): Integer;
begin
  if ABase <= 0 then Result := 0 else Result := ABase + AIndex;
end;

{ ------------------------------ TFBMetaScanner ------------------------------ }

constructor TFBMetaScanner.Create(AOwner: TComponent);
begin
  inherited Create(AOwner);
  FFindings := TList<TFBFinding>.Create;
  FSeen := TList<TComponent>.Create;
  FIncludeDataModules := True;

  Width := 760;
  Height := 440;
  BevelOuter := bvNone;
  Caption := '';
  ShowCaption := False;

  FTop := TPanel.Create(Self);
  FTop.Parent := Self;
  FTop.Align := alTop;
  FTop.Height := 36;
  FTop.BevelOuter := bvNone;
  FTop.Caption := '';
  FTop.ShowCaption := False;

  FBtnForm := MakeButton('Varrer Form', 6, 100, BtnFormClick);
  FBtnUnit := MakeButton('Varrer Unit...', 112, 110, BtnUnitClick);
  FBtnProject := MakeButton('Varrer Projeto...', 228, 120, BtnProjectClick);
  FBtnCopy := MakeButton('Copiar', 354, 70, BtnCopyClick);
  FBtnClear := MakeButton('Limpar', 430, 70, BtnClearClick);

  FStatus := TLabel.Create(Self);
  FStatus.Parent := FTop;
  FStatus.Left := 512;
  FStatus.Top := 11;
  FStatus.Caption := 'Pronto.';

  FDetail := TMemo.Create(Self);
  FDetail.Parent := Self;
  FDetail.Align := alBottom;
  FDetail.Height := 110;
  FDetail.ReadOnly := True;
  FDetail.ScrollBars := ssVertical;
  FDetail.WordWrap := True;

  FList := TListView.Create(Self);
  FList.Parent := Self;
  FList.Align := alClient;
  FList.ViewStyle := vsReport;
  FList.ReadOnly := True;
  FList.RowSelect := True;
  FList.GridLines := True;
  FList.HideSelection := False;
  with FList.Columns.Add do begin Caption := 'Sev.'; Width := 60; end;
  with FList.Columns.Add do begin Caption := 'Local'; Width := 230; end;
  with FList.Columns.Add do begin Caption := 'Linha'; Width := 50; end;
  with FList.Columns.Add do begin Caption := 'Problema'; Width := 380; end;
  FList.OnSelectItem := ListSelectItem;
  FList.OnCustomDrawItem := ListCustomDrawItem;
end;

destructor TFBMetaScanner.Destroy;
begin
  FSeen.Free;
  FFindings.Free;
  inherited;
end;

function TFBMetaScanner.MakeButton(const ACaption: string; ALeft, AWidth: Integer;
  AHandler: TNotifyEvent): TButton;
begin
  Result := TButton.Create(Self);
  Result.Parent := FTop;
  Result.SetBounds(ALeft, 5, AWidth, 26);
  Result.Caption := ACaption;
  Result.OnClick := AHandler;
end;

procedure TFBMetaScanner.Notification(AComponent: TComponent; Operation: TOperation);
begin
  inherited;
  if Operation = opRemove then
  begin
    if AComponent = FConnection then FConnection := nil;
    if AComponent = FTargetForm then FTargetForm := nil;
  end;
end;

procedure TFBMetaScanner.SetConnection(const Value: TFDConnection);
begin
  if FConnection <> Value then
  begin
    FConnection := Value;
    if Value <> nil then Value.FreeNotification(Self);
  end;
end;

procedure TFBMetaScanner.SetTargetForm(const Value: TCustomForm);
begin
  if FTargetForm <> Value then
  begin
    FTargetForm := Value;
    if Value <> nil then Value.FreeNotification(Self);
  end;
end;

{ ------------------------------- botoes / UI -------------------------------- }

procedure TFBMetaScanner.BtnFormClick(Sender: TObject);
begin
  ScanForm;
end;

procedure TFBMetaScanner.BtnUnitClick(Sender: TObject);
begin
  ScanUnit('');
end;

procedure TFBMetaScanner.BtnProjectClick(Sender: TObject);
begin
  ScanProject('');
end;

procedure TFBMetaScanner.BtnCopyClick(Sender: TObject);
begin
  Clipboard.AsText := ReportText;
  FStatus.Caption := 'Relatorio copiado para a area de transferencia.';
end;

procedure TFBMetaScanner.BtnClearClick(Sender: TObject);
begin
  Clear;
end;

procedure TFBMetaScanner.ListSelectItem(Sender: TObject; Item: TListItem;
  Selected: Boolean);
var
  F: TFBFinding;
begin
  if not Selected or (Item = nil) then Exit;
  F := FFindings[Integer(NativeInt(Item.Data))];
  FDetail.Text := F.Msg + sLineBreak + sLineBreak + 'Como corrigir: ' + F.Fix;
end;

procedure TFBMetaScanner.ListCustomDrawItem(Sender: TCustomListView; Item: TListItem;
  State: TCustomDrawState; var DefaultDraw: Boolean);
begin
  case FFindings[Integer(NativeInt(Item.Data))].Severity of
    fsError: Sender.Canvas.Font.Color := clRed;
    fsWarning: Sender.Canvas.Font.Color := clWebDarkOrange;
    fsInfo: Sender.Canvas.Font.Color := clNavy;
  end;
end;

procedure TFBMetaScanner.SetBusy(ABusy: Boolean; const AText: string);
begin
  FTop.Enabled := not ABusy;
  if AText <> '' then FStatus.Caption := AText;
  if ABusy then Application.ProcessMessages;
end;

procedure TFBMetaScanner.AddFinding(ASev: TFBSeverity; const ASource: string;
  ALine: Integer; const AMsg, AFix: string);
var
  F: TFBFinding;
begin
  F.Severity := ASev;
  F.Source := ASource;
  F.Line := ALine;
  F.Msg := AMsg;
  F.Fix := AFix;
  FFindings.Add(F);
end;

procedure TFBMetaScanner.Clear;
begin
  FFindings.Clear;
  FSeen.Clear;
  FList.Items.Clear;
  FDetail.Clear;
  FStatus.Caption := 'Pronto.';
end;

procedure TFBMetaScanner.BeginScan;
begin
  Clear;
  FFoundFBConn := False;
  FFoundLink := False;
  FCurSource := '';
  FRootDir := '';
end;

procedure TFBMetaScanner.RefreshList;
var
  i: Integer;
  F: TFBFinding;
begin
  FFindings.Sort(TComparer<TFBFinding>.Construct(
    function(const A, B: TFBFinding): Integer
    begin
      Result := Ord(A.Severity) - Ord(B.Severity);
      if Result = 0 then Result := CompareText(A.Source, B.Source);
      if Result = 0 then Result := A.Line - B.Line;
    end));
  FList.Items.BeginUpdate;
  try
    FList.Items.Clear;
    for i := 0 to FFindings.Count - 1 do
    begin
      F := FFindings[i];
      with FList.Items.Add do
      begin
        Caption := SevText[F.Severity];
        SubItems.Add(F.Source);
        if F.Line > 0 then SubItems.Add(IntToStr(F.Line)) else SubItems.Add('');
        SubItems.Add(F.Msg);
        Data := Pointer(NativeInt(i));
      end;
    end;
  finally
    FList.Items.EndUpdate;
  end;
end;

procedure TFBMetaScanner.EndScan;
var
  E, W, I: Integer;
  F: TFBFinding;
begin
  E := 0; W := 0; I := 0;
  for F in FFindings do
    case F.Severity of
      fsError: Inc(E);
      fsWarning: Inc(W);
    else
      Inc(I);
    end;
  if (E = 0) and (W = 0) then
    AddFinding(fsInfo, 'Resumo', 0,
      'Nenhum problema obvio encontrado nesta varredura.',
      'Se o erro -817 persistir, execute "select MON$SQL_DIALECT from MON$DATABASE" no ' +
      'banco real e logue o SQL exato que dispara o erro (ele costuma ser um DDL ' +
      'ou um UPDATE/INSERT em tabela RDB$).');
  RefreshList;
  SetBusy(False, Format('%d erro(s), %d aviso(s), %d info.', [E, W, I]));
  if FList.Items.Count > 0 then
    FList.Items[0].Selected := True;
end;

function TFBMetaScanner.ErrorCount: Integer;
var
  F: TFBFinding;
begin
  Result := 0;
  for F in FFindings do
    if F.Severity = fsError then Inc(Result);
end;

function TFBMetaScanner.ReportText: string;
var
  SL: TStringList;
  F: TFBFinding;
begin
  SL := TStringList.Create;
  try
    for F in FFindings do
    begin
      if F.Line > 0 then
        SL.Add(Format('[%s] %s (linha %d): %s', [SevText[F.Severity], F.Source, F.Line, F.Msg]))
      else
        SL.Add(Format('[%s] %s: %s', [SevText[F.Severity], F.Source, F.Msg]));
      SL.Add('    -> ' + F.Fix);
    end;
    Result := SL.Text;
  finally
    SL.Free;
  end;
end;

{ ------------------------------ varredura viva ------------------------------ }

procedure TFBMetaScanner.ScanForm;
var
  F: TCustomForm;
  i: Integer;
begin
  BeginScan;
  SetBusy(True, 'Analisando componentes do form...');
  try
    F := FTargetForm;
    if F = nil then F := GetParentForm(Self);
    if F <> nil then ScanComponents(F, F.Name)
    else AddFinding(fsInfo, 'Form', 0, 'Nenhum form alvo encontrado.',
      'Defina a propriedade TargetForm ou coloque o componente dentro de um form.');

    if FIncludeDataModules then
      for i := 0 to Screen.DataModuleCount - 1 do
        ScanComponents(Screen.DataModules[i], Screen.DataModules[i].Name);

    if FConnection <> nil then
      CheckComponent(FConnection, FConnection.Name);

    CheckLoadedClient;
  finally
    EndScan;
  end;
end;

procedure TFBMetaScanner.ScanComponents(AOwner: TComponent; const APath: string);
var
  i: Integer;
  C: TComponent;
begin
  for i := 0 to AOwner.ComponentCount - 1 do
  begin
    C := AOwner.Components[i];
    if C is TFrame then
      ScanComponents(C, APath + '.' + C.Name)
    else
      CheckComponent(C, APath + '.' + C.Name);
  end;
end;

procedure TFBMetaScanner.CheckComponent(C: TComponent; const AWhere: string);
var
  SL: TStringList;
  j: Integer;
begin
  if FSeen.IndexOf(C) >= 0 then Exit;
  FSeen.Add(C);

  if C is TFDConnection then
    CheckConnection(TFDConnection(C), AWhere)
  else if C is TFDTransaction then
    CheckTransaction(TFDTransaction(C), AWhere)
  else if C is TFDPhysFBDriverLink then
    CheckDriverLink(TFDPhysFBDriverLink(C), AWhere)
  else if C is TFDScript then
  begin
    SL := TStringList.Create;
    try
      for j := 0 to TFDScript(C).SQLScripts.Count - 1 do
        SL.AddStrings(TFDScript(C).SQLScripts[j].SQL);
      ScanSQLLines(SL, AWhere, 0, True, True);
    finally
      SL.Free;
    end;
  end
  else if C is TFDQuery then
    ScanSQLLines(TFDQuery(C).SQL, AWhere, 0, True, False)
  else if C is TFDCommand then
    ScanSQLLines(TFDCommand(C).CommandText, AWhere, 0, True, False);
end;

procedure TFBMetaScanner.CheckConnection(AConn: TFDConnection; const AWhere: string);
var
  Drv, D: string;
  DV: Integer;
begin
  Drv := Trim(AConn.Params.Values['DriverID']);
  if Drv = '' then Drv := Trim(AConn.DriverName);
  if (Drv <> '') and not SameText(Drv, 'FB') then Exit;
  FFoundFBConn := True;

  if AConn.ConnectionDefName <> '' then
    AddFinding(fsInfo, AWhere, 0,
      Format('A conexao usa ConnectionDefName "%s": Dialect e demais parametros vem do ' +
        'FDConnectionDefs.ini.', [AConn.ConnectionDefName]),
      'Confira se a definicao tem Dialect=3 (e execute a varredura de Projeto para ler o .ini).')
  else
  begin
    D := Trim(AConn.Params.Values['Dialect']);
    if D = '' then
      AddFinding(fsWarning, AWhere, 0,
        'Parametro Dialect nao definido explicitamente na conexao.', FIX_DIALECT)
    else if D <> '3' then
      AddFinding(fsError, AWhere, 0,
        Format('Dialect=%s na conexao. O Firebird 5 deve ser usado com Dialect=3.', [D]),
        FIX_DIALECT);
  end;

  if AConn.TxOptions.ReadOnly then
    AddFinding(fsError, AWhere, 0,
      'TxOptions.ReadOnly = True: a transacao padrao e somente leitura e bloqueia DDL.',
      FIX_RO);
  if AConn.UpdateOptions.ReadOnly then
    AddFinding(fsWarning, AWhere, 0,
      'UpdateOptions.ReadOnly = True na conexao.', FIX_RO);
  if Assigned(AConn.Transaction) and AConn.Transaction.Options.ReadOnly then
    AddFinding(fsError, AWhere, 0,
      'A transacao associada (Connection.Transaction) esta com Options.ReadOnly = True.',
      FIX_RO);
  if not AConn.TxOptions.AutoCommit then
    AddFinding(fsInfo, AWhere, 0,
      'TxOptions.AutoCommit = False: DDL so e efetivado apos Commit explicito.',
      'Chame Connection.Commit logo apos cada DDL, antes de usar o novo objeto em DML.');

  if AConn.Connected then
    CheckLiveDatabase(AConn, AWhere);
end;

procedure TFBMetaScanner.CheckLiveDatabase(AConn: TFDConnection; const AWhere: string);
var
  V: Variant;
  Dlg: Integer;
begin
  try
    V := AConn.ExecSQLScalar('select MON$SQL_DIALECT from MON$DATABASE');
    if not VarIsNull(V) then
    begin
      Dlg := V;
      if Dlg <> 3 then
        AddFinding(fsError, AWhere, 0,
          Format('O BANCO conectado esta em dialeto %d (MON$SQL_DIALECT).', [Dlg]), FIX_DIALECT)
      else
        AddFinding(fsInfo, AWhere, 0, 'Banco conectado em dialeto 3 (OK).', 'Nada a fazer.');
    end;

    V := AConn.ExecSQLScalar('select MON$READ_ONLY from MON$DATABASE');
    if (not VarIsNull(V)) and (Integer(V) = 1) then
      AddFinding(fsError, AWhere, 0, 'O banco esta em modo READ ONLY.',
        'Use: gfix -mode read_write <banco> (com acesso exclusivo).');

    V := AConn.ExecSQLScalar('select MON$READ_ONLY from MON$TRANSACTIONS ' +
      'where MON$TRANSACTION_ID = current_transaction');
    if (not VarIsNull(V)) and (Integer(V) = 1) then
      AddFinding(fsError, AWhere, 0, 'A transacao atual esta READ ONLY (verificado no servidor).',
        FIX_RO);

    V := AConn.ExecSQLScalar('select rdb$get_context(''SYSTEM'',''ENGINE_VERSION'') from rdb$database');
    if not VarIsNull(V) then
      AddFinding(fsInfo, AWhere, 0, 'Versao do servidor Firebird: ' + VarToStr(V), 'Informativo.');
  except
    on E: Exception do
      AddFinding(fsInfo, AWhere, 0,
        'Nao foi possivel consultar o banco: ' + E.Message,
        'Verifique se o usuario pode ler as tabelas MON$.');
  end;
end;

procedure TFBMetaScanner.CheckTransaction(ATx: TFDTransaction; const AWhere: string);
begin
  if ATx.Options.ReadOnly then
    AddFinding(fsError, AWhere, 0,
      'TFDTransaction.Options.ReadOnly = True: DDL nao e permitido nesta transacao.',
      FIX_RO);
  if not ATx.Options.AutoCommit then
    AddFinding(fsInfo, AWhere, 0,
      'Options.AutoCommit = False: lembre de dar Commit apos DDL.',
      'Chame Commit logo apos o DDL.');
end;

procedure TFBMetaScanner.CheckDriverLink(ALink: TFDPhysFBDriverLink; const AWhere: string);
begin
  FFoundLink := True;
  if Trim(ALink.VendorLib) = '' then
    AddFinding(fsWarning, AWhere, 0,
      'VendorLib nao definido: o FireDAC carrega a primeira fbclient.dll encontrada no PATH.',
      'Aponte VendorLib para a fbclient.dll do Firebird 5 com a MESMA arquitetura do exe (32/64 bits).')
  else
    CheckClientLib(ALink.VendorLib, AWhere, 0);
end;

function TFBMetaScanner.ResolveLib(const APath: string): string;
var
  Root: string;
begin
  Result := APath;
  if TPath.IsRelativePath(APath) then
  begin
    Root := '';
    if FRootDir <> '' then Root := IncludeTrailingPathDelimiter(FRootDir);
    if (ExtractFilePath(APath) <> '') and (Root <> '') and FileExists(Root + APath) then
      Exit(Root + APath);
    if FileExists(ExtractFilePath(ParamStr(0)) + APath) then
      Exit(ExtractFilePath(ParamStr(0)) + APath);
    if (Root <> '') and FileExists(Root + APath) then
      Exit(Root + APath);
    if ExtractFilePath(APath) = '' then
    begin
      Result := FileSearch(APath, GetEnvironmentVariable('PATH'));
      if Result = '' then Result := APath;
    end;
  end;
end;

procedure TFBMetaScanner.CheckClientLib(const APath, AWhere: string; ALine: Integer);
var
  Full: string;
  Bits: Integer;
  Ma, Mi, Re, Bu: Word;
begin
  if ContainsText(APath, 'gds32') or ContainsText(APath, 'fbembed') then
    AddFinding(fsWarning, AWhere, ALine,
      'Biblioteca cliente antiga/embutida (gds32/fbembed): ' + APath,
      'Use a fbclient.dll do Firebird 5.0.');
  Full := ResolveLib(APath);
  if not FileExists(Full) then
  begin
    AddFinding(fsWarning, AWhere, ALine,
      'Biblioteca cliente nao encontrada: ' + APath,
      'Confira o caminho de VendorLib / VendorHome.');
    Exit;
  end;
  Bits := GetPEBits(Full);
  if (Bits <> 0) and (Bits <> SizeOf(Pointer) * 8) then
    AddFinding(fsError, AWhere, ALine,
      Format('A DLL %s e de %d bits, mas este executavel e de %d bits.',
        [Full, Bits, SizeOf(Pointer) * 8]),
      'Use a fbclient.dll com a mesma arquitetura do executavel.');
  if GetFileVer(Full, Ma, Mi, Re, Bu) then
  begin
    AddFinding(fsInfo, AWhere, ALine,
      Format('Cliente: %s (versao %d.%d.%d.%d, %d bits).', [Full, Ma, Mi, Re, Bu, Bits]),
      'Informativo.');
    if Ma < 5 then
      AddFinding(fsWarning, AWhere, ALine,
        Format('fbclient.dll versao %d.x e anterior ao servidor 5.0.', [Ma]),
        'Troque pela fbclient.dll do Firebird 5.0 para evitar divergencias de protocolo/dialeto.');
  end;
end;

procedure TFBMetaScanner.CheckLoadedClient;
var
  H: HMODULE;
  Buf: array[0..MAX_PATH] of Char;
begin
  H := GetModuleHandle('fbclient.dll');
  if H <> 0 then
  begin
    GetModuleFileName(H, Buf, Length(Buf));
    CheckClientLib(string(Buf), 'fbclient.dll carregada no processo', 0);
  end
  else if FFoundFBConn and not FFoundLink then
    AddFinding(fsInfo, 'Ambiente', 0,
      'fbclient.dll ainda nao foi carregada e nao ha TFDPhysFBDriverLink no form.',
      'Conecte e varra novamente para ver qual DLL esta em uso, ou adicione um ' +
      'TFDPhysFBDriverLink com VendorLib.');
end;

{ ---------------------------- analise de texto SQL --------------------------- }

function TFBMetaScanner.ScanSQLLines(ALines: TStrings; const AWhere: string;
  ABaseLine: Integer; AComponentMode, AMultiOK: Boolean): Integer;
var
  i, FirstDDL, FirstDML, Semi: Integer;
  S, T: string;
  HasType: Boolean;
  M: TMatch;
begin
  Result := 0;
  FirstDDL := -1;
  FirstDML := -1;
  Semi := 0;
  HasType := False;
  for i := 0 to ALines.Count - 1 do
  begin
    S := ALines[i];
    T := Trim(S);
    if T.StartsWith('//') then Continue;

    if TRegEx.IsMatch(S, RX_SYSTAB, [roIgnoreCase]) then
      AddFinding(fsError, AWhere, LineOf(ABaseLine, i),
        'Alteracao direta em tabela de sistema (RDB$...).',
        'O Firebird nao permite alterar metadados via UPDATE/INSERT/DELETE em RDB$ tabelas. ' +
        'Use DDL (ALTER TABLE, ALTER DOMAIN, COMMENT ON...).');

    if TRegEx.IsMatch(S, RX_SETDIALECT, [roIgnoreCase]) then
      AddFinding(fsError, AWhere, LineOf(ABaseLine, i),
        '"SET SQL DIALECT" enviado pela aplicacao.',
        'Dialeto nao se muda por SQL dinamico. Use Dialect=3 na conexao e gfix para o banco.');

    if TRegEx.IsMatch(S, RX_ALTERDB, [roIgnoreCase]) then
      AddFinding(fsWarning, AWhere, LineOf(ABaseLine, i),
        'ALTER DATABASE detectado.',
        'Exige SYSDBA/dono do banco e, em geral, acesso exclusivo; nao use em transacao read-only.');

    M := TRegEx.Match(S, RX_DIALECT, [roIgnoreCase]);
    if M.Success and (M.Groups[1].Value <> '3') then
      AddFinding(fsError, AWhere, LineOf(ABaseLine, i),
        Format('Dialeto %s atribuido/configurado aqui.', [M.Groups[1].Value]), FIX_DIALECT);

    if TRegEx.IsMatch(S, RX_DDL, [roIgnoreCase]) then
    begin
      Inc(Result);
      if FirstDDL < 0 then FirstDDL := i;
    end;
    if AComponentMode then
    begin
      if (FirstDML < 0) and TRegEx.IsMatch(S, RX_DML, [roIgnoreCase]) then FirstDML := i;
      Semi := Semi + Length(S) - Length(StringReplace(S, ';', '', [rfReplaceAll]));
    end;
    if (not HasType) and TRegEx.IsMatch(S, RX_TYPES, [roIgnoreCase]) then HasType := True;
  end;

  if Result > 0 then
  begin
    AddFinding(fsInfo, AWhere, LineOf(ABaseLine, FirstDDL),
      Format('Comando DDL (metadados) detectado: %d ocorrencia(s).', [Result]), FIX_DDL);
    if AComponentMode and (not AMultiOK) and (FirstDML >= 0) then
      AddFinding(fsWarning, AWhere, LineOf(ABaseLine, FirstDML),
        'DDL e DML misturados no mesmo comando/dataset.',
        'Separe: execute o DDL, de Commit, e so depois rode os INSERT/UPDATE que usam o novo objeto.');
    if AComponentMode and (not AMultiOK) and (Semi > 1) then
      AddFinding(fsWarning, AWhere, LineOf(ABaseLine, FirstDDL),
        'Possivel script com varios comandos num TFDQuery/TFDCommand.',
        'Use TFDScript para varios comandos (ou um TFDCommand por comando).');
    if HasType then
      AddFinding(fsInfo, AWhere, LineOf(ABaseLine, FirstDDL),
        'O DDL usa tipos exclusivos do dialeto 3 (BIGINT/DATE/TIME/TIMESTAMP/DECIMAL/NUMERIC).',
        'Se o banco estiver em dialeto 1, esses tipos geram -817. Confirme MON$SQL_DIALECT = 3.');
  end;
end;

{ ---------------------------- varredura de arquivos --------------------------- }

function TFBMetaScanner.RelName(const AFile: string): string;
begin
  if FRootDir <> '' then
    Result := ExtractRelativePath(IncludeTrailingPathDelimiter(FRootDir), AFile)
  else
    Result := ExtractFileName(AFile);
end;

procedure TFBMetaScanner.ScanUnit(const AFileName: string);
var
  FN, Dfm: string;
begin
  FN := AFileName;
  if FN = '' then
    with TOpenDialog.Create(nil) do
    try
      Filter := 'Units Delphi (*.pas)|*.pas|Todos os arquivos (*.*)|*.*';
      Title := 'Escolha a unit a analisar';
      if not Execute then Exit;
      FN := FileName;
    finally
      Free;
    end;

  BeginScan;
  SetBusy(True, 'Analisando ' + ExtractFileName(FN) + '...');
  try
    FRootDir := ExtractFilePath(FN);
    ScanFile(FN);
    Dfm := ChangeFileExt(FN, '.dfm');
    if FileExists(Dfm) and not SameText(FN, Dfm) then ScanFile(Dfm);
  finally
    EndScan;
  end;
end;

procedure TFBMetaScanner.ScanProject(const ADir: string);
var
  Dir, F, Ext, Up: string;
  Files: TArray<string>;
  n: Integer;
begin
  Dir := ADir;
  if Dir = '' then Dir := FProjectDir;
  if Dir = '' then
    with TFileOpenDialog.Create(nil) do
    try
      Options := [fdoPickFolders];
      Title := 'Escolha a pasta do projeto';
      if not Execute then Exit;
      Dir := FileName;
    finally
      Free;
    end;

  BeginScan;
  SetBusy(True, 'Listando arquivos...');
  try
    FRootDir := Dir;
    try
      Files := TDirectory.GetFiles(Dir, '*.*', TSearchOption.soAllDirectories);
    except
      on E: Exception do
      begin
        AddFinding(fsInfo, Dir, 0, 'Falha ao listar a pasta: ' + E.Message, 'Verifique permissoes.');
        Exit;
      end;
    end;
    n := 0;
    for F in Files do
    begin
      Up := UpperCase(F);
      if ContainsText(Up, '\__HISTORY\') or ContainsText(Up, '\__RECOVERY\') or
         ContainsText(Up, '\WIN32\') or ContainsText(Up, '\WIN64\') or
         ContainsText(Up, '\.GIT\') then Continue;
      Ext := LowerCase(ExtractFileExt(F));
      if (Ext = '.pas') or (Ext = '.dfm') or
         ((Ext = '.ini') and StartsText('FDConnectionDefs', ExtractFileName(F))) then
      begin
        Inc(n);
        if n mod 5 = 0 then SetBusy(True, 'Analisando ' + ExtractFileName(F) + '...');
        ScanFile(F);
      end;
    end;
    AddFinding(fsInfo, 'Resumo', 0, Format('%d arquivo(s) analisado(s) em %s.', [n, Dir]),
      'Informativo.');
  finally
    EndScan;
  end;
end;

procedure TFBMetaScanner.ScanFile(const AFile: string);
var
  Ext: string;
  SL: TStringList;
begin
  Ext := LowerCase(ExtractFileExt(AFile));
  FCurSource := RelName(AFile);
  if (Ext = '.dfm') and IsBinaryDfm(AFile) then
  begin
    AddFinding(fsInfo, FCurSource, 0, 'DFM em formato binario: nao analisado.',
      'No IDE: clique direito no form > "Text DFM" (ou Tools > Options > Form Designer: "New forms as text").');
    Exit;
  end;
  SL := TStringList.Create;
  try
    try
      SL.LoadFromFile(AFile);
    except
      on E: Exception do
      begin
        AddFinding(fsInfo, FCurSource, 0, 'Nao foi possivel ler o arquivo: ' + E.Message, 'Verifique o arquivo.');
        Exit;
      end;
    end;
    if Ext = '.dfm' then ScanDfm(SL)
    else if Ext = '.pas' then ScanPas(SL)
    else if Ext = '.ini' then ScanIni(SL);
  finally
    SL.Free;
  end;
end;

procedure TFBMetaScanner.ScanPas(ALines: TStrings);
var
  i, nDDL: Integer;
  S: string;
  M: TMatch;
begin
  nDDL := ScanSQLLines(ALines, FCurSource, 1, False, False);

  for i := 0 to ALines.Count - 1 do
  begin
    S := ALines[i];
    if Trim(S).StartsWith('//') then Continue;

    if TRegEx.IsMatch(S, 'ReadOnly\s*:=\s*True', [roIgnoreCase]) then
      AddFinding(fsWarning, FCurSource, i + 1,
        'ReadOnly := True atribuido. Se for na conexao/transacao que executa DDL, causa bloqueio.',
        FIX_RO);

    M := TRegEx.Match(S, 'VendorLib\s*:=\s*''([^'']+)''', [roIgnoreCase]);
    if M.Success then
      CheckClientLib(M.Groups[1].Value, FCurSource, i + 1)
    else if TRegEx.IsMatch(S, '(gds32|fbembed)\.dll', [roIgnoreCase]) then
      AddFinding(fsWarning, FCurSource, i + 1,
        'Referencia a gds32.dll/fbembed.dll (cliente antigo).',
        'Use a fbclient.dll do Firebird 5.0.');
  end;

  if (nDDL > 0) and not TRegEx.IsMatch(ALines.Text, RX_COMMIT, [roIgnoreCase]) then
    AddFinding(fsWarning, FCurSource, 0,
      'Esta unit executa DDL mas nao ha Commit visivel.',
      'Se AutoCommit=False, de Commit logo apos o DDL. Se AutoCommit=True, ignore este aviso.');
end;

procedure TFBMetaScanner.ScanIni(ALines: TStrings);
var
  i: Integer;
  M: TMatch;
  HasFB: Boolean;
begin
  HasFB := TRegEx.IsMatch(ALines.Text, 'DriverID\s*=\s*FB', [roIgnoreCase]);
  if not HasFB then Exit;
  for i := 0 to ALines.Count - 1 do
  begin
    M := TRegEx.Match(ALines[i], '^\s*Dialect\s*=\s*(\d+)', [roIgnoreCase]);
    if M.Success and (M.Groups[1].Value <> '3') then
      AddFinding(fsError, FCurSource, i + 1,
        Format('Dialect=%s na ConnectionDef.', [M.Groups[1].Value]), FIX_DIALECT);
  end;
  if not TRegEx.IsMatch(ALines.Text, '^\s*Dialect\s*=', [roIgnoreCase, roMultiLine]) then
    AddFinding(fsWarning, FCurSource, 0,
      'ConnectionDef Firebird sem parametro Dialect.', FIX_DIALECT);
end;

procedure TFBMetaScanner.ScanDfm(ALines: TStrings);
var
  i, Depth, BlockDepth, BlockStart: Integer;
  T, Cls, Nm: string;
  InBlock: Boolean;
  Block: TStringList;
  M: TMatch;
begin
  Depth := 0;
  BlockDepth := 0;
  BlockStart := 0;
  InBlock := False;
  Cls := '';
  Nm := '';
  Block := TStringList.Create;
  try
    for i := 0 to ALines.Count - 1 do
    begin
      T := Trim(ALines[i]);
      if InBlock then Block.Add(ALines[i]);

      if StartsText('object ', T) or StartsText('inherited ', T) or StartsText('inline ', T) then
      begin
        Inc(Depth);
        if not InBlock then
        begin
          M := TRegEx.Match(T, '^(?:object|inherited|inline)\s+(\w+)\s*:\s*(\w+)', [roIgnoreCase]);
          if M.Success and IsRelevantClass(M.Groups[2].Value) then
          begin
            InBlock := True;
            BlockDepth := Depth;
            BlockStart := i + 1;
            Nm := M.Groups[1].Value;
            Cls := M.Groups[2].Value;
            Block.Clear;
            Block.Add(ALines[i]);
          end;
        end;
      end
      else if SameText(T, 'item') then
        Inc(Depth)
      else if (T = 'end') or (T = 'end>') then
      begin
        if InBlock and (Depth = BlockDepth) then
        begin
          AnalyzeDfmBlock(Cls, Nm, Block, BlockStart);
          InBlock := False;
        end;
        Dec(Depth);
      end;
    end;
  finally
    Block.Free;
  end;
end;

procedure TFBMetaScanner.AnalyzeDfmBlock(const ACls, AName: string; ABlock: TStrings;
  AStartLine: Integer);
var
  Where, Txt, Lib: string;
  M: TMatch;
  i: Integer;
  IsFB: Boolean;
begin
  Where := FCurSource + ' > ' + AName;
  Txt := ABlock.Text;

  if SameText(ACls, 'TFDConnection') then
  begin
    IsFB := TRegEx.IsMatch(Txt, 'DriverID\s*=\s*FB\b', [roIgnoreCase]) or
            TRegEx.IsMatch(Txt, 'DriverName\s*=\s*''FB''', [roIgnoreCase]);
    if TRegEx.IsMatch(Txt, 'ConnectionDefName\s*=', [roIgnoreCase]) then
    begin
      AddFinding(fsInfo, Where, AStartLine,
        'Conexao usa ConnectionDefName (parametros no FDConnectionDefs.ini).',
        'Confira Dialect=3 no .ini (a varredura de Projeto le arquivos FDConnectionDefs*.ini).');
      IsFB := True;
    end
    else if not IsFB then Exit
    else
    begin
      M := TRegEx.Match(Txt, '''Dialect\s*=\s*(\d+)''', [roIgnoreCase]);
      if not M.Success then
        AddFinding(fsWarning, Where, AStartLine,
          'Params sem Dialect=3 explicito.', FIX_DIALECT)
      else if M.Groups[1].Value <> '3' then
        AddFinding(fsError, Where, AStartLine,
          Format('Dialect=%s nos Params.', [M.Groups[1].Value]), FIX_DIALECT);
    end;

    for i := 0 to ABlock.Count - 1 do
    begin
      if TRegEx.IsMatch(ABlock[i], '^\s*(TxOptions|Options)\.ReadOnly\s*=\s*True', [roIgnoreCase]) then
        AddFinding(fsError, Where, AStartLine + i,
          'TxOptions.ReadOnly = True: transacao somente leitura bloqueia DDL.', FIX_RO);
      if TRegEx.IsMatch(ABlock[i], '^\s*UpdateOptions\.ReadOnly\s*=\s*True', [roIgnoreCase]) then
        AddFinding(fsWarning, Where, AStartLine + i,
          'UpdateOptions.ReadOnly = True na conexao.', FIX_RO);
      if TRegEx.IsMatch(ABlock[i], '^\s*TxOptions\.AutoCommit\s*=\s*False', [roIgnoreCase]) then
        AddFinding(fsInfo, Where, AStartLine + i,
          'AutoCommit = False: DDL so vale apos Commit.',
          'Chame Commit logo apos o DDL.');
    end;
  end
  else if SameText(ACls, 'TFDTransaction') then
  begin
    for i := 0 to ABlock.Count - 1 do
      if TRegEx.IsMatch(ABlock[i], '^\s*Options\.ReadOnly\s*=\s*True', [roIgnoreCase]) then
        AddFinding(fsError, Where, AStartLine + i,
          'TFDTransaction com Options.ReadOnly = True: bloqueia DDL.', FIX_RO);
  end
  else if SameText(ACls, 'TFDPhysFBDriverLink') then
  begin
    FFoundLink := True;
    M := TRegEx.Match(Txt, 'VendorLib\s*=\s*''([^'']*)''', [roIgnoreCase]);
    if (not M.Success) or (Trim(M.Groups[1].Value) = '') then
      AddFinding(fsWarning, Where, AStartLine,
        'VendorLib nao definido: usa a fbclient.dll encontrada no PATH.',
        'Aponte VendorLib para a fbclient.dll do Firebird 5.0 (mesma arquitetura do exe).')
    else
    begin
      Lib := M.Groups[1].Value;
      CheckClientLib(Lib, Where, AStartLine);
    end;
  end
  else
    ScanSQLLines(ABlock, Where, AStartLine, True, SameText(ACls, 'TFDScript'));
end;

end.
