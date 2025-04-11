// Todas as funções foram feitas com toda ajuda possível da internet
// (vídeos [os poucos que existem], blogs, sites e todos os chats possíveis)
// pois eu não tinha como rodar para saber onde existiam erros

// Coloquei um comentário explicando a ideia do que cada rule e a invariant deveriam fazer
// para pelo menos explicar a minha intenção, mesmo que o código esteja incorreto

methods {
    function _exists(uint256 id) external returns (bool) envfree;
    function _allTokensIndex(uint256 id) external returns (uint256) envfree;
    function _allTokens(uint256 index) external returns (Token) envfree;
    function _addressData(address owner) external returns (AddressData) envfree;
    function balanceOf(uint256 tokenId) external returns (uint256) envfree;
    function ownerOf(uint256 tokenId) external returns (address) envfree;
    function totalSupply() external returns (uint256) envfree;
    function slotOf(uint256 tokenId) external returns (uint256) envfree;

    function transferFrom(uint256 fromTokenId, uint256 toTokenId, uint256 value) external;
    function transferFrom(address from, address to, uint256 tokenId) external;
    
    function _approveValue(uint256 tokenId, address spender, uint256 value) external;
    function _approve(address to, uint256 tokenId) external;
    function getApproved(uint256 tokenId) external returns (address) envfree;
    function allowance(uint256 tokenId, address spender) external returns (uint256) envfree;

    function _mint(address to, uint256 tokenId, uint256 slot, uint256 value) external;
    function _burn(uint256 tokenId) external;

    function _isApprovedOrOwner(address operator, uint256 tokenId) external returns (bool) envfree;
}

// Essa garante a ideia de que cada token tem um índice único no _allTokensIndex
// Caso essa regra não seja atendida, poderia causar erro ao tentar acessar os dados de um token
rule tokenIdUniqueness {
    forall uint id1, uint id2 where id1 != id2 {
        _allTokensIndex[id1] != _allTokensIndex[id2]
    }
}

// Essa regra garante que o token está batendo corretamente com o dono do token
// Se um token existe, ele deve estar presente no array de tokens do dono
rule ownerConsistency {
    forall uint id {
        _exists(id) => 
            _allTokens[_allTokensIndex[id]].owner == _addressData[_allTokens[_allTokensIndex[id]].owner].ownedTokens[
                _addressData[_allTokens[_allTokensIndex[id]].owner].ownedTokensIndex[id]
            ]
    }
}

// Uma regra básica, mas muito importante, basicamente garante que ao fazer
// uma transferência com o transferFrom, a soma dos tokens dos contratos devem ser
// a mesma, no início e no final da transferência.
rule balanceConsistencyAfterTransfer {
    env e;
    uint fromId;
    uint toId;
    uint value;

    require(_exists(fromId), "From token must exist");
    require(_exists(toId), "To token must exist");
    require(fromId != toId, "Transfer should be between different tokens");
    require(balanceOf(fromId) >= value, "Insufficient balance");

    uint initialFromBalance = balanceOf(fromId);
    uint initialToBalance = balanceOf(toId);

    transferFrom(fromId, toId, value) @with(e);

    assert balanceOf(fromId) == initialFromBalance - value &&
           balanceOf(toId) == initialToBalance + value;
}

// Essa garante que todas as aprovações do token a ser transferido sejam finalizadas/limpas
// Para que não fique pendências antigas no token que agora vai ter um novo dono
rule approvalClearingOnTransfer {
    env e;
    uint id;
    address newOwner;

    require(_exists(id), "Token must exist");
    address originalOwner = ownerOf(id);
    require(newOwner != originalOwner, "New owner must be different");

    _approveValue(id, address(0x123), 100);
    _approve(address(0x456), id);

    transferFrom(originalOwner, newOwner, id) @with(e);

    assert getApproved(id) == address(0) &&
           allowance(id, address(0x123)) == 0;
}

// Essa regra, basicamente, garante o token permaneça inalterado após sua criação
// Coloquei um transferFrom para fazer uma operação com o token e depois conferir
//  se os seus dados (slot) estão iguais
rule slotConsistency {
    env e;
    uint id = require(_exists(id), "Token must exist");
    uint originalSlot = slotOf(id);

    transferFrom(ownerOf(id), address(0xABC), id) @with(e);

    assert slotOf(id) == originalSlot;
}

// Apenas garante que o número de tokens é igual ao tamanho do _allTokens
// Isso nos diz, de certa forma, que não existem tokens inexistentes sendo considerados como existentes ou tokens duplicados
rule totalSupplyConsistency {
    assert totalSupply() == _allTokens.length;
}

// Essa regra checa se o "sistema" realmente sabe com quem cada token está
rule ownerEnumerationConsistency {
    forall address owner, uint index {
        index < balanceOf(owner) =>
            _addressData[owner].ownedTokensIndex[_addressData[owner].ownedTokens[index]] == index
    }
}

// Essa regra vai checar se quando ocorre um mint de um token, o número de tokens aumenta em 1
rule mintIncreasesSupply {
    env e;
    uint initialSupply = totalSupply();

    _mint(address(0x123), 999, 1, 100) @with(e);

    assert totalSupply() == initialSupply + 1;
}

// Regra contrária da anterior, vai checar se quando fazemos o burn de um token, o número de tokens diminui em 1
rule burnDecreasesSupply {
    env e;
    uint id = require(_exists(id), "Token must exist");
    uint initialSupply = totalSupply();

    _burn(id) @with(e);

    assert totalSupply() == initialSupply - 1;
}

// Regra que garante que se o usuário quiser transferir um token que não é dele, ele precisa ter a autorização
rule valueTransferAllowance {
    env e;
    uint fromId = require(_exists(fromId), "From token must exist");
    uint toId = require(_exists(toId), "To token must exist");
    address operator = e.msg.sender;
    uint value = nondet;

    !_isApprovedOrOwner(operator, fromId) =>
        require(allowance(fromId, operator) >= value, "Insufficient allowance");

    transferFrom(fromId, toId, value) @with(e);
}

// Garante que a soma de todos os tokens de todos os usuários seja sempre a mesma
// Com exceção de casos como mint e burn de tokens
invariant totalValueConservation ignoreFuncs: [_mint, mint, _burn, burn] {
    uint initialSum = 0;
    forall uint i in 0.._allTokens.length-1 {
        initialSum += _allTokens[i].balance;
    }

    havoc();

    uint finalSum = 0;
    forall uint i in 0.._allTokens.length-1 {
        finalSum += _allTokens[i].balance;
    }

    assert finalSum == initialSum;
}